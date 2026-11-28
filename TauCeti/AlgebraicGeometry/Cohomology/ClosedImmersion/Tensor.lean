/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Basic
public import TauCeti.AlgebraicGeometry.LineBundle.Monoidal
import TauCeti.AlgebraicGeometry.VectorBundle.ProjectionFormula

/-!
# Cohomology of twists along a closed immersion

For a closed immersion `i : X ⟶ Y`, the projection formula for an invertible sheaf `L` on `Y`
identifies `(i_* F) ⊗ L ≅ i_* (F ⊗ i^* L)`. Combined with the closed-immersion cohomology
comparison (`TauCeti.AlgebraicGeometry.cohomologyPushforwardIso`), this shows that
`H^q(X, F ⊗ K)` vanishes if and only if `H^q(Y, i_* F ⊗ L)` vanishes for any `K ≅ i^* L`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.subsingleton_cohomology_tensor_pullback_iff_pushforward_tensor`:
  cohomology vanishing for twists along a closed immersion.
-/

public section

open CategoryTheory AlgebraicGeometry MonoidalCategory BraidedCategory

namespace AlgebraicGeometry.Scheme.Hom

open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules Scheme.Modules

universe u

noncomputable section

/-- **Cohomology vanishing for twists along a closed immersion.** For a closed immersion
`i : X ⟶ Y`, a sheaf `F` on `X`, an invertible sheaf `L` on `Y`, and an identification
`epb : i^* L ≅ K`, `H^q(X, F ⊗ K)` vanishes if and only if `H^q(Y, i_* F ⊗ L)` vanishes. -/
theorem subsingleton_cohomology_tensor_pullback_iff_pushforward_tensor
    {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i] (F : X.Modules) (L : Y.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible Y L] {K : X.Modules}
    (epb : (Scheme.Modules.pullback i).obj L ≅ K) (q : ℕ) :
    Subsingleton (Cohomology (F ⊗ K) q) ↔
      Subsingleton (Cohomology ((pushforward i).obj F ⊗ L) q) := by
  let L' := (TauCeti.AlgebraicGeometry.InvertibleSheaf.toFiniteLocallyFree Y).obj ⟨L, inferInstance⟩
  let epb' : ((FiniteLocallyFreeSheaf.pullback i).obj L').obj ≅ K :=
    eqToIso (FiniteLocallyFreeSheaf.pullback_obj_obj i L') ≪≫ epb
  let e : (pushforward i).obj F ⊗ L ≅ (pushforward i).obj (F ⊗ K) :=
    β_ ((pushforward i).obj F) L ≪≫
      (FiniteLocallyFreeSheaf.pushforwardTensorLeftIso i L').app F ≪≫
      (pushforward i).mapIso (whiskerRightIso epb' F ≪≫ β_ K F)
  have hpush : Subsingleton (Cohomology ((pushforward i).obj (F ⊗ K)) q) ↔
      Subsingleton (Cohomology (F ⊗ K) q) :=
    Equiv.subsingleton_congr
      (cohomologyPushforwardIso i (F ⊗ K) q).addCommGroupIsoToAddEquiv.toEquiv
  exact hpush.symm.trans (Scheme.Modules.subsingleton_cohomology_congr e q).symm

end

end AlgebraicGeometry.Scheme.Hom
