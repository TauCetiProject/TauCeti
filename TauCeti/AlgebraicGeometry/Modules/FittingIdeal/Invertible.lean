/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Basic
public import TauCeti.AlgebraicGeometry.Modules.FittingIdeal.Pullback
import TauCeti.AlgebraicGeometry.IdealSheaf.Locality
import TauCeti.AlgebraicGeometry.Modules.Pullback.Quasicoherent

/-!
# Invariance of Fitting ideal sheaves under twisting by a line bundle

Tensoring a finite-type quasi-coherent `𝒪_X`-module `N` by an invertible sheaf `K` does not change
any of its Fitting ideal sheaves: on an open cover trivializing `K`, the pullback of `N ⊗ K` is
isomorphic to the pullback of `N`, and Fitting ideal sheaves commute with arbitrary pullback and
depend only on the isomorphism class of the module.

## Main results

* `AlgebraicGeometry.Scheme.Modules.fittingIdeal_tensor_of_isInvertible`:
  `Fitt_k(N ⊗ K) = Fitt_k(N)` for every `k : ℕ`, finite-type quasi-coherent `N`, and invertible
  sheaf `K`.

## References

* [The Stacks Project, Tag 0C3C](https://stacks.math.columbia.edu/tag/0C3C) (Fitting ideals of
  finite-type quasi-coherent modules).
-/

public section

open CategoryTheory MonoidalCategory AlgebraicGeometry TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

/-- Tensoring a finite-type quasi-coherent `𝒪_X`-module `N` by an invertible `𝒪_X`-module `K`
leaves all of its Fitting ideal sheaves unchanged. -/
theorem fittingIdeal_tensor_of_isInvertible {X : Scheme.{u}} (N : X.Modules) [N.IsQuasicoherent]
    [N.IsFiniteType] (K : X.Modules) [hK : SheafOfModules.isInvertible X K] (k : ℕ) :
    (N ⊗ K).fittingIdeal
        (fun U ↦ Scheme.Modules.finite_sections_of_isAffineOpen _ U.val U.property) k =
      N.fittingIdeal
        (fun U ↦ Scheme.Modules.finite_sections_of_isAffineOpen _ U.val U.property) k := by
  obtain ⟨ι, W, hW, htriv⟩ :=
    (SheafOfModules.isInvertible_iff_exists_isOpenCover (X := X) (M := K)).mp hK
  refine Scheme.IdealSheafData.ext_of_comap_openCover (X.openCoverOfIsOpenCover W hW) fun i ↦ ?_
  -- `(X.openCoverOfIsOpenCover W hW).f i` is `(W i).ι`, whereas `rw` fails implicit checking on
  -- `U.2 : U ∈ X.affineOpens` inside the finiteness witness of `fittingIdeal`.
  change ((N ⊗ K).fittingIdeal _ k).comap (W i).ι = (N.fittingIdeal _ k).comap (W i).ι
  rw [← Scheme.Modules.fittingIdeal_pullback (W i).ι (N ⊗ K) k,
    ← Scheme.Modules.fittingIdeal_pullback (W i).ι N k]
  let eK : (Scheme.Modules.pullback (W i).ι).obj K ≅ 𝟙_ (W i : Scheme).Modules :=
    ((Scheme.Modules.restrictFunctorIsoPullback (W i).ι).app K).symm ≪≫ (htriv i).some.symm
  let e : (Scheme.Modules.pullback (W i).ι).obj (N ⊗ K) ≅
      (Scheme.Modules.pullback (W i).ι).obj N :=
    asIso (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback (W i).ι) N K) ≪≫
      whiskerLeftIso ((Scheme.Modules.pullback (W i).ι).obj N) eK ≪≫
      ρ_ ((Scheme.Modules.pullback (W i).ι).obj N)
  exact Scheme.Modules.fittingIdeal_congr _ e k

end

end AlgebraicGeometry.Scheme.Modules
