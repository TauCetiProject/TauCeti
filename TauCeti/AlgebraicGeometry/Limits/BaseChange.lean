/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import TauCeti.CategoryTheory.Limits.Shapes.Pullback.Cofiltered

/-!
# Base change of a cofiltered diagram of schemes

Let `D : I ⥤ Scheme` be a diagram, `i : I`, and `r : Z ⟶ Dᵢ`. The base change
`D.pullbackOver r : Over i ⥤ Scheme`, `j ↦ Dⱼ ×_{Dᵢ} Z`, writes a scheme `Z` over a member `Dᵢ`
of `S = lim Dⱼ` as the cofiltered limit of the `Dⱼ ×_{Dᵢ} Z` (Stacks, Section 32.10 (01ZL)). This
file records that affine transition maps, quasi-compactness and quasi-separation of the members
pass to the base change, so that the descent results for such limits apply to it.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.Scheme

variable {I : Type*} [Category* I] (D : I ⥤ Scheme.{u}) {i : I} {Z : Scheme.{u}}
  (r : Z ⟶ D.obj i)

instance [∀ {j k : I} (f : j ⟶ k), IsAffineHom (D.map f)] {j k : Over i} (f : j ⟶ k) :
    IsAffineHom ((D.pullbackOver r).map f) := by
  have s : IsPullback ((D.pullbackOver r).map f ≫ pullback.snd (D.map k.hom) r)
      (pullback.fst _ _) r (D.map f.left ≫ D.map k.hom) := by
    rw [Functor.pullbackOver_map_snd, ← D.map_comp, Over.w f]
    exact (IsPullback.of_hasPullback _ r).flip
  have sq := IsPullback.of_right s (D.pullbackOver_map_fst r f)
    (IsPullback.of_hasPullback _ r).flip
  exact MorphismProperty.of_isPullback sq.flip inferInstance

instance [∀ j, CompactSpace (D.obj j)] [QuasiCompact r] (j : Over i) :
    CompactSpace ((D.pullbackOver r).obj j) := by
  dsimp; infer_instance

instance [∀ j, QuasiSeparatedSpace (D.obj j)] [QuasiSeparated r] (j : Over i) :
    QuasiSeparatedSpace ((D.pullbackOver r).obj j) := by
  dsimp; exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst _ _)

end TauCeti.AlgebraicGeometry.Scheme
