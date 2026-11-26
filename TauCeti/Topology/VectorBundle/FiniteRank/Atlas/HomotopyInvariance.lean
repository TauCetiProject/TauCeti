/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.CoordinateHom
public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Pullback
public import TauCeti.Topology.VectorBundle.FiniteRank.HomotopyInvariance

/-!
# Homotopy invariance of pullbacks of variable-rank bundle atlases

Over a paracompact R₁ base `X`, for instance a paracompact Hausdorff space, the pullbacks of a
variable-rank atlas `A : FiniteRankAtlas 𝕜 Y` along homotopic maps `f₀ f₁ : C(X, Y)` are isomorphic
(`TauCeti.FiniteRankAtlas.nonempty_pullback_iso_pullback_of_homotopic`). The scalars `𝕜` form a
complete normed `ℝ`-algebra, such as `ℝ` or `ℂ`. No bounded-rank, finite-cover or compactness
hypothesis is needed.

The rank of `A` is locally constant, so it is constant along each track `t ↦ H (t, x)` of a
homotopy `H` from `f₀` to `f₁`. Hence on the clopen locus of `X` where both pulled-back ranks equal
`n`, the homotopy restricts to a homotopy of maps into the rank-`n` stratum of `Y`, and the
constant-rank theorem `TauCeti.FiniteRankBundleCore.nonempty_pullback_iso_pullback_of_homotopic`
applies to the rank-`n` stratum core of `A`, the clopen locus being again paracompact. These
stratumwise isomorphisms assemble by `TauCeti.FiniteRankAtlas.ofStratumCoordinateHom` into a bundle
map which is bijective on every fibre, hence an isomorphism
(`TauCeti.FiniteRankAtlas.isIso_iff_bijective`).

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.2, Theorem 1.6.
-/

public section

open Bundle CategoryTheory unitInterval

namespace TauCeti.FiniteRankAtlas

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y]
  (A : FiniteRankAtlas 𝕜 Y) {f₀ f₁ : C(X, Y)}

/-- The rank of an atlas is constant along each track of a homotopy. -/
private theorem rank_homotopy_apply (H : f₀.Homotopy f₁) (t : I) (x : X) :
    A.rank (H (t, x)) = A.rank (f₀ x) := by
  rw [← H.apply_zero x]
  exact (A.rank.isLocallyConstant.comp_continuous
    (H.continuous.comp (Continuous.prodMk_left x))).apply_eq_of_preconnectedSpace t 0

/-- On the locus where both pulled-back ranks are `n`, a homotopy from `f₀` to `f₁` is a homotopy
of maps into the rank-`n` stratum of `Y`. -/
private def stratumHomotopy (H : f₀.Homotopy f₁) (n : ℕ) :
    ((f₀.restrictPreimage {y | A.rank y = n}).comp
        (stratumPairFst (A.pullback f₀) (A.pullback f₁) n n)).Homotopy
      ((f₁.restrictPreimage {y | A.rank y = n}).comp
        (stratumPairSnd (A.pullback f₀) (A.pullback f₁) n n)) where
  toFun p := ⟨H (p.1, p.2.val), (A.rank_homotopy_apply H p.1 p.2.val).trans p.2.property.1⟩
  continuous_toFun := (H.continuous.comp
    (continuous_fst.prodMk (continuous_subtypeVal.comp continuous_snd))).subtype_mk _
  map_zero_left x := Subtype.ext <| (H.apply_zero x.val).trans <| congrArg Subtype.val <|
    congrArg (f₀.restrictPreimage {y | A.rank y = n}) (stratumPairFst_apply _ _ n n x).symm
  map_one_left x := Subtype.ext <| (H.apply_one x.val).trans <| congrArg Subtype.val <|
    congrArg (f₁.restrictPreimage {y | A.rank y = n}) (stratumPairSnd_apply _ _ n n x).symm

variable [NormedAlgebra ℝ 𝕜] [CompleteSpace 𝕜] [R1Space X] [ParacompactSpace X]

/-- On the locus where both pulled-back ranks are `n`, the pullbacks of the rank-`n` stratum core
of `A` along the two ends of a homotopy are isomorphic. -/
private theorem nonempty_stratumIso (H : f₀.Homotopy f₁) (n : ℕ) :
    Nonempty (((A.pullback f₀).stratumCore n).pullback
        (stratumPairFst (A.pullback f₀) (A.pullback f₁) n n) ≅
      ((A.pullback f₁).stratumCore n).pullback
        (stratumPairSnd (A.pullback f₀) (A.pullback f₁) n n)) := by
  have hS : IsClosed {x : X | (A.pullback f₀).rank x = n ∧ (A.pullback f₁).rank x = n} :=
    ((A.pullback f₀).rank.isLocallyConstant.isClopen_fiber n).isClosed.inter
      ((A.pullback f₁).rank.isLocallyConstant.isClopen_fiber n).isClosed
  have : ParacompactSpace (StratumPair (A.pullback f₀) (A.pullback f₁) n n) :=
    hS.isClosedEmbedding_subtypeVal.paracompactSpace
  -- The stratum cores of the two pullbacks are pullbacks of the stratum core of `A`
  -- (`stratumCore_pullback`), and a pullback of a pullback is literally the pullback along the
  -- composite (`FiniteRankBundleCore.pullback_comp`); both hold by `rfl`.
  exact (A.stratumCore n).nonempty_pullback_iso_pullback_of_homotopic ⟨A.stratumHomotopy H n⟩

/-- The coordinate morphisms on the joint rank strata of the two pullbacks: the chosen
isomorphism on the diagonal strata, and zero on the others, which are empty. -/
private noncomputable def stratumHom (H : f₀.Homotopy f₁) (m n : ℕ) :
    StratumCoordinateHom (A.pullback f₀) (A.pullback f₁) m n :=
  if h : m = n then by subst h; exact (A.nonempty_stratumIso H m).some.hom else 0

/-- The coordinate morphisms `stratumHom` are bijective on every fibre: the joint rank strata off
the diagonal are empty, and on the diagonal they are isomorphisms. -/
private theorem bijective_fiberMap_stratumHom (H : f₀.Homotopy f₁) (m n : ℕ)
    (x : StratumPair (A.pullback f₀) (A.pullback f₁) m n) :
    Function.Bijective ((A.stratumHom H m n).fiberMap x) := by
  obtain rfl : m = n := by
    have h₁ := A.rank_homotopy_apply H 1 x.val
    rw [H.apply_one] at h₁
    exact x.property.1.symm.trans (h₁.symm.trans x.property.2)
  simp only [stratumHom, ↓reduceDIte]
  exact (FiniteRankBundleCore.isIso_iff_bijective _).1 inferInstance x

/-- **Homotopy invariance of variable-rank bundles.** Over a paracompact R₁ base, the pullbacks of
a variable-rank atlas along homotopic maps are isomorphic. -/
theorem nonempty_pullback_iso_pullback_of_homotopic (h : f₀.Homotopic f₁) :
    Nonempty (A.pullback f₀ ≅ A.pullback f₁) := by
  obtain ⟨H⟩ := h
  have := (isIso_iff_bijective (ofStratumCoordinateHom (A.stratumHom H))).2 fun x ↦ by
    rw [fiberMap_ofStratumCoordinateHom, ContinuousLinearMap.coe_coe]
    exact A.bijective_fiberMap_stratumHom H _ _ _
  exact ⟨asIso (ofStratumCoordinateHom (A.stratumHom H))⟩

end TauCeti.FiniteRankAtlas
