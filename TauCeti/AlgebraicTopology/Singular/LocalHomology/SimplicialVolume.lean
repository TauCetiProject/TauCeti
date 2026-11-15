/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.L1Norm

/-!
# The simplicial volume of a closed oriented manifold

Let `M` be a compact oriented topological `n`-manifold without boundary, with orientation `o`
(`TauCeti.HomologicalOrientation M E n`). Its **simplicial volume** (Gromov's norm)
`o.simplicialVolume hn` is the `ℓ¹`-seminorm (`SSet.homologyL1Seminorm`) of its real fundamental
class: the infimum of `∑ |aᵢ|` over all real singular cycles `∑ aᵢ σᵢ` representing the image
`o.realFundamentalClass hn ∈ Hₙ(M; ℝ)` of the integral fundamental class.

The simplicial volume is a homotopy invariant, and it is controlled by degrees of maps.

* **Degree inequality.** If a map `f : M → N` to a compact oriented `n`-manifold carries the
  fundamental class of `M` to `d` times that of `N`, then `|d| * ‖N‖ ≤ ‖M‖`
  (`TauCeti.HomologicalOrientation.abs_mul_simplicialVolume_le`). Indeed the image of a real cycle
  representing `[M]` is a cycle of no larger `ℓ¹`-norm representing `d • [N]`, and the `ℓ¹`-seminorm
  of `d • [N]` is `|d|` times that of `[N]`.
* **Self-maps of large degree.** A manifold with a self-map of degree `d`, `|d| > 1`, has
  simplicial volume `0` (`TauCeti.HomologicalOrientation.simplicialVolume_eq_zero_of_one_lt_abs`).
* **Homotopy invariance.** Homotopy equivalent compact connected oriented manifolds have the same
  simplicial volume, for any choice of orientations
  (`TauCeti.HomologicalOrientation.simplicialVolume_eq_of_homotopyEquiv`): a homotopy equivalence
  carries the fundamental class to `±` the fundamental class. In particular the simplicial volume of
  a compact connected manifold does not depend on the orientation.

The simplicial volume connects topology to Riemannian geometry: by the proportionality theorem of
Gromov and Thurston, the volume of a closed hyperbolic `n`-manifold is `vₙ` times its simplicial
volume, where `vₙ` is the volume of a regular ideal simplex in hyperbolic `n`-space. Since the
simplicial volume depends only on the homotopy type, so does the hyperbolic volume. The
proportionality theorem is not proved here.

## Main definitions

* `TauCeti.HomologicalOrientation.simplicialVolume`: the simplicial volume `‖M‖`.

## Main results

* `TauCeti.HomologicalOrientation.abs_mul_simplicialVolume_le`: the degree inequality.
* `TauCeti.HomologicalOrientation.simplicialVolume_eq_zero_of_one_lt_abs`: the simplicial volume
  vanishes in the presence of a self-map of degree `d` with `|d| > 1`.
* `TauCeti.HomologicalOrientation.simplicialVolume_eq_of_homotopyEquiv`: homotopy invariance.

## References

* M. Gromov, *Volume and bounded cohomology*, Publ. Math. IHÉS 56 (1982), 5–99, Section 0.2.
* W. P. Thurston, *The Geometry and Topology of Three-Manifolds*, Princeton lecture notes
  (1978–1980), Chapter 6, Section 6.1 (Gromov's invariant and the proportionality theorem).
* R. Benedetti, C. Petronio, *Lectures on Hyperbolic Geometry*, Springer Universitext (1992),
  Chapter C (the Gromov norm and the proof of Mostow's rigidity theorem).
-/

public section

noncomputable section

open CategoryTheory Module AlgebraicTopology

namespace TauCeti

namespace HomologicalOrientation

variable {M E : Type} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {n : ℕ} (o : HomologicalOrientation M E n) (hn : finrank ℝ E = n) [CompactSpace M]

/-- The change of coefficients `Hₙ(X; ℤ) → Hₙ(X; ℝ)` on singular homology. -/
private abbrev toReal (X : TopCat.{0}) :
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).obj X ⟶
      ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ ℝ)).obj X :=
  ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).map intToRealCoeff).app X

/-- The **simplicial volume** `‖M‖` of a compact oriented manifold (Gromov's norm): the
`ℓ¹`-seminorm of its real fundamental class, that is, the infimum of `∑ |aᵢ|` over the real
singular cycles `∑ aᵢ σᵢ` representing it. -/
def simplicialVolume : ℝ :=
  (TopCat.toSSet.obj (TopCat.of M)).homologyL1Seminorm (o.realFundamentalClass hn)

/-- The simplicial volume is the `ℓ¹`-seminorm of the real fundamental class. -/
theorem simplicialVolume_def :
    o.simplicialVolume hn =
      (TopCat.toSSet.obj (TopCat.of M)).homologyL1Seminorm (o.realFundamentalClass hn) :=
  (rfl)

/-- The simplicial volume is nonnegative. -/
theorem simplicialVolume_nonneg : 0 ≤ o.simplicialVolume hn :=
  SSet.homologyL1Seminorm_nonneg _ _

/-- The simplicial volume does not depend on the sign of the orientation. -/
@[simp]
theorem simplicialVolume_neg : (-o).simplicialVolume hn = o.simplicialVolume hn := by
  rw [simplicialVolume_def, simplicialVolume_def, realFundamentalClass_neg,
    SSet.homologyL1Seminorm_neg]

variable {N E' : Type} [TopologicalSpace N] [T2Space N]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [ChartedSpace E' N]
  (o' : HomologicalOrientation N E' n) (hn' : finrank ℝ E' = n) [CompactSpace N]

omit [T2Space N] [CompactSpace N] in
/-- The real image of the fundamental class under `f` has `ℓ¹`-seminorm at most `‖M‖`. -/
private theorem homologyL1Seminorm_toReal_mapFundamentalClass_le (f : C(M, N)) :
    (TopCat.toSSet.obj (TopCat.of N)).homologyL1Seminorm
        ((toReal (n := n) (TopCat.of N)).hom (o.mapFundamentalClass hn f)) ≤
      o.simplicialVolume hn := by
  -- Changing coefficients commutes with the map induced by `f`.
  have h : (toReal (n := n) (TopCat.of N)).hom (o.mapFundamentalClass hn f) =
      (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom f)) (ModuleCat.of ℤ ℝ) n).hom
        (o.realFundamentalClass hn) := by
    rw [mapFundamentalClass_def, realFundamentalClass_def]
    exact congrArg (fun g ↦ g.hom (o.fundamentalClass hn))
        (((singularHomologyFunctor (ModuleCat.{0} ℤ) n).map intToRealCoeff).naturality
          (TopCat.ofHom f))
  rw [h]
  exact SSet.homologyL1Seminorm_homologyMap_le _ _ _

/-- **The degree inequality for the simplicial volume.** If `f : M → N` carries the fundamental
class of `M` to `d` times the fundamental class of `N`, then `|d| * ‖N‖ ≤ ‖M‖`. -/
theorem abs_mul_simplicialVolume_le (f : C(M, N)) {d : ℤ}
    (hf : o.mapFundamentalClass hn f = d • o'.fundamentalClass hn') :
    |(d : ℝ)| * o'.simplicialVolume hn' ≤ o.simplicialVolume hn := by
  have h := o.homologyL1Seminorm_toReal_mapFundamentalClass_le hn f
  -- `toReal` of the fundamental class of `N` is its real fundamental class.
  have h' : (toReal (n := n) (TopCat.of N)).hom (d • o'.fundamentalClass hn') =
      d • o'.realFundamentalClass hn' := by
    rw [realFundamentalClass_def]
    exact map_zsmul _ d _
  rwa [hf, h', SSet.homologyL1Seminorm_zsmul, Int.norm_eq_abs] at h

/-- **Self-maps of large degree.** If `M` has a self-map carrying its fundamental class to `d`
times itself with `|d| > 1`, then the simplicial volume of `M` vanishes. -/
theorem simplicialVolume_eq_zero_of_one_lt_abs (f : C(M, M)) {d : ℤ}
    (hf : o.mapFundamentalClass hn f = d • o.fundamentalClass hn) (hd : 1 < |d|) :
    o.simplicialVolume hn = 0 := by
  have h := o.abs_mul_simplicialVolume_le hn o hn f hf
  have hd' : (1 : ℝ) < |(d : ℝ)| := by exact_mod_cast hd
  nlinarith [o.simplicialVolume_nonneg hn]

variable [ConnectedSpace N] [ConnectedSpace M]

/-- **Homotopy invariance of the simplicial volume.** Homotopy equivalent compact connected
oriented manifolds have the same simplicial volume, whatever their orientations. -/
theorem simplicialVolume_eq_of_homotopyEquiv (e : ContinuousMap.HomotopyEquiv M N) :
    o.simplicialVolume hn = o'.simplicialVolume hn' := by
  obtain ⟨d, hd⟩ := o'.exists_eq_zsmul_fundamentalClass hn' (o.mapFundamentalClass hn e.toFun)
  obtain ⟨d', hd'⟩ := o.exists_eq_zsmul_fundamentalClass hn (o'.mapFundamentalClass hn' e.invFun)
  -- The composite `e.invFun ∘ e.toFun` is homotopic to the identity, so it carries the fundamental
  -- class of `M` to itself; it also carries it to `d * d'` times itself.
  have key : (d * d') • o.fundamentalClass hn = o.fundamentalClass hn := by
    have h₁ : o.mapFundamentalClass hn (e.invFun.comp e.toFun) = o.fundamentalClass hn := by
      rw [o.mapFundamentalClass_eq_of_homotopic hn e.left_inv, mapFundamentalClass_id]
    have h₂ : o.mapFundamentalClass hn (e.invFun.comp e.toFun) =
        d • o'.mapFundamentalClass hn' e.invFun := by
      rw [mapFundamentalClass_comp, hd, mapFundamentalClass_def]
      exact map_zsmul _ d _
    rw [hd'] at h₂
    rw [← smul_smul]
    -- `h₂` and `h₁` are equations in the singular homology functor's object, which is the
    -- simplicial homology of the singular simplicial set by definition.
    exact h₂.symm.trans h₁
  have h1 : d * d' = 1 :=
    (o.fundamentalClassEquiv hn).injective (by
      rw [fundamentalClassEquiv_apply, fundamentalClassEquiv_apply, one_smul]
      exact key)
  have habs : |(d : ℝ)| = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' h1 with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  have habs' : |(d' : ℝ)| = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' h1 with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp
  have h := o.abs_mul_simplicialVolume_le hn o' hn' e.toFun hd
  have h' := o'.abs_mul_simplicialVolume_le hn' o hn e.invFun hd'
  rw [habs, one_mul] at h
  rw [habs', one_mul] at h'
  exact le_antisymm h' h

/-- Homeomorphic compact connected oriented manifolds have the same simplicial volume. -/
theorem simplicialVolume_eq_of_homeomorph (e : M ≃ₜ N) :
    o.simplicialVolume hn = o'.simplicialVolume hn' :=
  o.simplicialVolume_eq_of_homotopyEquiv hn o' hn' e.toHomotopyEquiv

/-- The simplicial volume of a compact connected manifold does not depend on the orientation. -/
theorem simplicialVolume_eq_of_orientation (o₁ : HomologicalOrientation M E n) :
    o.simplicialVolume hn = o₁.simplicialVolume hn :=
  o.simplicialVolume_eq_of_homotopyEquiv hn o₁ hn (ContinuousMap.HomotopyEquiv.refl M)

end HomologicalOrientation

end TauCeti
