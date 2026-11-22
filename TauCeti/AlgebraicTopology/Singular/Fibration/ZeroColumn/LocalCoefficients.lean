/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Fibration.ZeroColumn.Basic
public import TauCeti.AlgebraicTopology.Cellular.LocalCoefficients.Coproduct
public import TauCeti.AlgebraicTopology.Cellular.LocalCoefficients.EdgeIncidence
public import TauCeti.AlgebraicTopology.Cellular.LocalCoefficients.Homology
public import TauCeti.AlgebraicTopology.Singular.Empty

/-!
# The column `p = 0` of the second page of the Serre spectral sequence with local coefficients

Let `p : E ⟶ B` be a Serre fibration and `C ⊆ B` a relative CW complex with skeleta `Xⁿ` and base
`X⁻¹ = D`. The fibre homology `b ↦ Hq(p⁻¹(b); R)` is a local coefficient system on `B` with
path-transport monodromy (`TauCeti.TopCat.serreFiberLocalSystem`); write `Hq(F)` for its restriction
to `C` (`TauCeti.TopCat.serreFiberLocalSystemOn`). This file identifies the column `p = 0` of the
second page of the Serre spectral sequence with the zeroth homology of the base with these
coefficients,

`E²_{0,q} ≅ H₀(C, D; Hq(F))`

(`TauCeti.TopCat.serreSpectralSequenceSecondPageXZeroIsoTwistedHomology`), through the cellular
homology in degree zero
(`TauCeti.TopCat.serreSpectralSequenceSecondPageXZeroIsoTwistedCellularHomology`). This is the
column `p = 0` of the classical identification `E²_{p,q} ≅ H_p(B; H_q(F))`.

The column `p = 0` of the second page is the quotient of the fibre homology over the `0`-skeleton
`E¹_{0,q} = Hq(p⁻¹(X⁰), p⁻¹(X⁻¹); R)` by the transport differences `a - τⱼ a` along the `1`-cells
(`TauCeti.TopCat.serreSpectralSequenceSecondPageXZeroIsoCokernel`). The cellular homology in degree
zero is the quotient of the cellular chain group `H₀(X⁰, X⁻¹; Hq(F))` by the image of the cellular
differential, which sends a `1`-cell to the difference of its two end points, each read through
the transport along the cell
(`TauCeti.twistedHomologyMap_characteristicCellPairMap_comp_twistedCellularDifferential_zero`).
The comparison has two steps.

* Both `E¹_{0,q}` and `H₀(X⁰, X⁻¹; Hq(F))` are the direct sum of the fibre homology over the
  centres of the `0`-cells (`TauCeti.TopCat.isColimitCofanFiberHomologyToPreimageSkeletonZero` and
  `TauCeti.isColimitCofanιTwistedHomology₀ZeroCellCenter`). This gives an isomorphism
  `Hq(p⁻¹(X⁰), p⁻¹(X⁻¹); R) ≅ H₀(X⁰, X⁻¹; Hq(F))` (`TauCeti.TopCat.serreZeroChainsIso`) which sends
  the class of a fibre homology class over any point of the `0`-skeleton to its class with local
  coefficients (`TauCeti.TopCat.fiberHomologyToPreimageSkeletonZero_comp_serreZeroChainsIso_hom`):
  over a point of `X⁻¹` both vanish, and every other point of `X⁰` is the centre of a `0`-cell.
* Under this isomorphism, the cellular differential of a `1`-cell `j` is the transport difference
  along `j`. The two end points of `D¹` are joined in the simply connected disk, and the
  characteristic map carries the segment between them to the path `TauCeti.cellPath` of the cell
  along which the transport `τⱼ` is taken. So the two maps have the same image and the two
  quotients agree.

## Main definitions

* `TauCeti.TopCat.serreFiberLocalSystemOn`: the local system of fibre homology on `C`.
* `TauCeti.TopCat.serreZeroChainsIso`: `Hq(p⁻¹(X⁰), p⁻¹(X⁻¹); R) ≅ H₀(X⁰, X⁻¹; Hq(F))`.
* `TauCeti.TopCat.serreSpectralSequenceSecondPageXZeroIsoTwistedCellularHomology`: `E²_{0,q}` is
  the cellular homology `H₀(C; Hq(F))`.
* `TauCeti.TopCat.serreSpectralSequenceSecondPageXZeroIsoTwistedHomology`: `E²_{0,q}` is the
  relative singular homology `H₀(C, D; Hq(F))`.

## Main results

* `TauCeti.TopCat.fiberHomologyToPreimageSkeletonZero_comp_serreZeroChainsIso_hom`: the
  identification of the column `p = 0` of the first page with the cellular chains on fibre classes.
* `TopCat.homologyπ_comp_serreSpectralSequenceSecondPageXZeroIsoTwistedCellularHomology_hom`: on
  the second page the identification is induced by that of the first page.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505, Chapter II.
* A. Hatcher,
  [*Spectral Sequences in Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/SSAT/SSch1.pdf),
  Chapter 1, the proof of Theorem 1.3 (the second page with local coefficients).
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Theorem 5.2.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Set Topology Topology.RelCWComplex

universe u

namespace TauCeti

namespace TopCat

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} [T2Space B] {C D : Set B} [RelCWComplex C D]

/-! ### The fibre homology over the `0`-skeleton is a coproduct over the `0`-cells -/

section FiberCofan

variable {R' : Type u} [Ring R']

/-- The unique point of the closed unit ball of `ℝ⁰`, lifted to the universe `u`. -/
private def ballPointZero : closedBall (0 : ULift.{u} (Fin 0 → ℝ)) 1 :=
  ⟨0, mem_closedBall_self zero_le_one⟩

/-- Every point of the closed unit ball of `ℝ⁰` is its centre. -/
private lemma eq_ballPointZero (x : closedBall (0 : ULift.{u} (Fin 0 → ℝ)) 1) :
    x = ballPointZero := Subsingleton.elim _ _

omit [T2Space B] in
/-- The characteristic map of a `0`-cell is constant at the centre of the cell. -/
private lemma cellULiftMap_zero_apply (k : cell C 0)
    (x : closedBall (0 : ULift.{u} (Fin 0 → ℝ)) 1) :
    cellULiftMap C 0 k x = map 0 k 0 := by
  rw [cellULiftMap_apply]
  exact congrArg (map 0 k) (Subsingleton.elim _ _)

variable (p) in
/-- Over a `0`-cell `k`, the pullback `Pₖ` of `p` along the characteristic map is the fibre of `p`
over the centre of the cell. -/
private def cellZeroPullbackHomeomorph (k : cell C 0) :
    p.fiber (map 0 k 0) ≃ₜ (cellDiskPullbackPair p C 0 k).fst where
  toFun e := ⟨(ballPointZero, e.val),
    (cellULiftMap_zero_apply k _).trans (p.apply_coe_fiber _ e).symm⟩
  invFun x := ⟨x.val.2, by
    rw [mem_preimage, mem_singleton_iff, ← x.property, cellULiftMap_zero_apply]⟩
  left_inv _ := rfl
  right_inv x := Subtype.ext (Prod.ext (eq_ballPointZero _).symm rfl)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

omit [T2Space B] in
/-- Over a `0`-cell, the part `∂Pₖ` of the pullback over the boundary sphere is empty. -/
instance isEmpty_cellDiskPullbackPair_zero_snd (k : cell C 0) :
    IsEmpty (cellDiskPullbackPair p C 0 k).snd := by
  refine ⟨fun x ↦ ?_⟩
  have h := ((mem_cellDiskPullbackPair_snd_iff 0 k x.val).1 x.property)
  rw [mem_sphere_zero_iff_norm] at h
  have h0 : ‖(x.val.val.1 : ULift.{u} (Fin 0 → ℝ))‖ = 0 := by
    rw [← ULift.norm_down]
    exact norm_eq_zero.2 (Subsingleton.elim _ _)
  exact zero_ne_one (h0.symm.trans h)

omit [T2Space B] in
/-- For a pair with empty subspace, ambient and relative homology agree. -/
private lemma isIso_singularHomologyπ_of_isEmpty (M : ModuleCat.{u} R') (q : ℕ) (P : TopPair.{u})
    [IsEmpty P.snd] : IsIso (P.singularHomologyπ M q) :=
  inferInstance

variable (R : Type u) [Ring R]

variable (p) in
/-- The identification `Hq(p⁻¹(χₖ(0)); R) ≅ Hq(Pₖ, ∂Pₖ; R)` over a `0`-cell `k`, induced by the
homeomorphism of the fibre with the pullback `Pₖ`, whose part `∂Pₖ` over the boundary is empty. -/
private def cellZeroFiberHomologyIso (q : ℕ) (k : cell C 0) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (p.fiber (map 0 k 0)) ≅
      (cellDiskPullbackPair p C 0 k).singularHomology (ModuleCat.of R R) q :=
  -- The two factors are isomorphisms; instance search does not see through the identification of
  -- the middle object as the singular homology of the ambient space, so they are supplied.
  @asIso _ _ _ _ (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
      (ModuleCat.of R R)).map (_root_.TopCat.isoOfHomeo (cellZeroPullbackHomeomorph p k)).hom ≫
    (cellDiskPullbackPair p C 0 k).singularHomologyπ (ModuleCat.of R R) q)
    (@IsIso.comp_isIso _ _ _ _ _ _ _ (Functor.map_isIso _ _)
      (isIso_singularHomologyπ_of_isEmpty (ModuleCat.of R R) q (cellDiskPullbackPair p C 0 k)))

/-- Read through `Hq(p⁻¹(χₖ(0))) ≅ Hq(Pₖ, ∂Pₖ)`, the projection of the pullback over a `0`-cell
to the skeletal filtration is the inclusion of the fibre over the centre. -/
private lemma cellZeroFiberHomologyIso_hom_comp (q : ℕ) (k : cell C 0) :
    (cellZeroFiberHomologyIso p R q k).hom ≫
        (cellDiskPullbackPair p C 0 k).singularHomologyMap (cellDiskPullbackPairMap p C 0 k)
          (ModuleCat.of R R) q =
      fiberHomologyToPreimageSkeletonZero p C R q
        (map_mem_skeletonLT_succ k (norm_zero.trans_le zero_le_one)) := by
  rw [cellZeroFiberHomologyIso, asIso_hom]
  -- The middle object is the ambient homology only up to unfolding `TopPair.toSSetPair`, so the
  -- composites are reassociated by unification rather than by rewriting.
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (TopPair.singularHomologyπ_naturality (R := ModuleCat.of R R)
    (cellDiskPullbackPairMap p C 0 k) q).symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  have hg : (_root_.TopCat.isoOfHomeo (cellZeroPullbackHomeomorph p k)).hom ≫
      TopPair.Hom.fst (cellDiskPullbackPairMap p C 0 k) =
        fiberToPreimageSkeletonZero p C
        (map_mem_skeletonLT_succ k (norm_zero.trans_le zero_le_one)) := by
    ext e
    exact Subtype.ext ((coe_cellDiskPullbackPairMap_fst_apply 0 k _).trans
      (coe_fiberToPreimageSkeletonZero_apply _ e).symm)
  rw [fiberHomologyToPreimageSkeletonZero_def, ← hg, Functor.map_comp]
  rfl

variable (C) (hp : serreFibrations p) in
/-- **The fibre homology over the `0`-skeleton is the direct sum of the fibre homology over the
`0`-cells.** The inclusions of the fibres over the centres of the `0`-cells exhibit
`Hq(p⁻¹(X⁰), p⁻¹(X⁻¹); R)` as the coproduct of the `Hq(p⁻¹(χₖ(0)); R)`. -/
def isColimitCofanFiberHomologyToPreimageSkeletonZero (q : ℕ) :
    IsColimit (Cofan.mk ((preimageSkeletonPair p C 0).singularHomology (ModuleCat.of R R) q)
      fun k : cell C 0 ↦ fiberHomologyToPreimageSkeletonZero p C R q
        (map_mem_skeletonLT_succ k (norm_zero.trans_le zero_le_one))) :=
  ((IsColimit.precomposeHomEquiv (Discrete.natIso fun k ↦ cellZeroFiberHomologyIso p R q k.as)
    _).symm (isColimitCofanSingularHomologyPreimageSkeletonPair C hp R 0 q)).ofIsoColimit
    (Cofan.ext (Iso.refl _) fun k ↦ by simp [Cofan.inj, cellZeroFiberHomologyIso_hom_comp])

end FiberCofan

/-! ### The fibre homology over the `0`-skeleton as cellular chains with local coefficients -/

section ZeroChains

variable (R : Type u) [Ring R] (hp : serreFibrations p)

variable (C) in
/-- The local system of fibre homology `b ↦ Hq(p⁻¹(b); R)` of a Serre fibration `p`, restricted to
the relative CW complex `C ⊆ B`. -/
abbrev serreFiberLocalSystemOn (q : ℕ) : LocalCoefficientSystem.{u, u, u} R (_root_.TopCat.of C) :=
  (LocalCoefficientSystem.pullback ⟨Subtype.val, continuous_subtypeVal⟩).obj
    (serreFiberLocalSystem hp (ModuleCat.of R R) q)

variable (C) in
/-- The class in the cellular chain group `H₀(X⁰, X⁻¹; Hq(F))` of a fibre homology class over a
point `y` of the `0`-skeleton. -/
def fiberHomologyToTwistedZeroChains (q : ℕ) (y : skeletonObj C 1) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (p.fiber (y : B)) ⟶
      twistedCellularChainGroup.{u, u, u} C (serreFiberLocalSystemOn C R hp q) 0 :=
  (serreFiberLocalSystemObjIso hp (ModuleCat.of R R) q (FundamentalGroupoid.mk (y : B))).inv ≫
    LocalCoefficientSystem.ιTwistedHomology₀
        (skeletonSystem C (serreFiberLocalSystemOn C R hp q) 1) y ≫
      (skeletonPair C 0).twistedHomologyπ _ 0

variable (C) in
/-- **The fibre homology over the `0`-skeleton is the cellular chain group in degree zero with
coefficients in the fibre homology.** The isomorphism
`Hq(p⁻¹(X⁰), p⁻¹(X⁻¹); R) ≅ H₀(X⁰, X⁻¹; Hq(F))` sends the class of a fibre homology class over a
point of the `0`-skeleton to its class with local coefficients
(`TauCeti.TopCat.fiberHomologyToPreimageSkeletonZero_comp_serreZeroChainsIso_hom`). -/
def serreZeroChainsIso (q : ℕ) :
    (preimageSkeletonPair p C 0).singularHomology (ModuleCat.of R R) q ≅
      twistedCellularChainGroup.{u, u, u} C (serreFiberLocalSystemOn C R hp q) 0 :=
  (isColimitCofanFiberHomologyToPreimageSkeletonZero C R hp q).coconePointUniqueUpToIso
    (((IsColimit.precomposeHomEquiv (Discrete.natIso fun k ↦ (serreFiberLocalSystemObjIso hp
        (ModuleCat.of R R) q (FundamentalGroupoid.mk (map 0 k.as 0))).symm) _).symm
      (isColimitCofanιTwistedHomology₀ZeroCellCenter C
        (serreFiberLocalSystemOn C R hp q))).ofIsoColimit
      (Cofan.ext (Iso.refl _) fun _ ↦ Category.comp_id _))

/-- A fibre homology class over a point of `X⁻¹` vanishes in `Hq(p⁻¹(X⁰), p⁻¹(X⁻¹); R)`. -/
private lemma fiberHomologyToPreimageSkeletonZero_eq_zero (q : ℕ) {b : B}
    (hb : b ∈ (skeletonLT C ((0 + 1 : ℕ) : ℕ∞) : Set B))
    (hb' : b ∈ (skeletonLT C (0 : ℕ∞) : Set B)) :
    fiberHomologyToPreimageSkeletonZero p C R q hb = 0 := by
  let g : p.fiber b ⟶ (preimageSkeletonPair p C 0).snd :=
    _root_.TopCat.ofHom ⟨fun e ↦ ⟨e.val, by
      rw [mem_preimage, p.apply_coe_fiber b e]; exact hb'⟩, by fun_prop⟩
  have hg : g ≫ (preimageSkeletonPair p C 0).map = fiberToPreimageSkeletonZero p C hb := by
    ext e
    exact Subtype.ext (coe_fiberToPreimageSkeletonZero_apply hb e).symm
  rw [fiberHomologyToPreimageSkeletonZero_def, ← hg, Functor.map_comp]
  -- The middle object is the ambient homology only up to unfolding `TopPair.toSSetPair`, so the
  -- composite is reassociated by unification rather than by rewriting.
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    ((preimageSkeletonPair p C 0).homologyMap_comp_singularHomologyπ (ModuleCat.of R R) q)).trans
      comp_zero)

/-- A coefficient over a point of `X⁻¹` has class zero in `H₀(X⁰, X⁻¹; L)`. -/
private lemma fiberHomologyToTwistedZeroChains_eq_zero (q : ℕ) (y : skeletonObj C 1)
    (hy : (y : B) ∈ (skeletonLT C (0 : ℕ∞) : Set B)) :
    fiberHomologyToTwistedZeroChains C R hp q y = 0 := by
  let y' : (skeletonPair C 0).snd := ⟨y, hy⟩
  have h := LocalCoefficientSystem.ιTwistedHomology₀_homologyMap
    (skeletonSystem C (serreFiberLocalSystemOn C R hp q) (0 + 1)) (skeletonPair C 0).map y'
  rw [fiberHomologyToTwistedZeroChains]
  refine (congrArg (_ ≫ ·) ((congrArg (· ≫ _) h.symm).trans ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) ((skeletonPair C 0).twistedHomologyMap_comp_twistedHomologyπ _ 0))))).trans ?_
  exact (congrArg (_ ≫ ·) comp_zero).trans comp_zero

variable (C) in
/-- Through `Hq(p⁻¹(X⁰), p⁻¹(X⁻¹); R) ≅ H₀(X⁰, X⁻¹; Hq(F))`, the class of a fibre homology class
over a point `y` of the `0`-skeleton is its class with local coefficients. -/
theorem fiberHomologyToPreimageSkeletonZero_comp_serreZeroChainsIso_hom
    (q : ℕ) (y : skeletonObj C 1) :
    fiberHomologyToPreimageSkeletonZero p C R q y.property ≫
        (serreZeroChainsIso C R hp q).hom =
      fiberHomologyToTwistedZeroChains C R hp q y := by
  rcases mem_skeletonLT_or_exists_map (n := 0) y.property with h | ⟨k, z, -, hz⟩
  · rw [fiberHomologyToPreimageSkeletonZero_eq_zero R q y.property h, zero_comp,
      fiberHomologyToTwistedZeroChains_eq_zero R hp q y h]
  · obtain rfl : y = zeroCellCenter C k :=
      Subtype.ext (hz.symm.trans (congrArg (map 0 k) (Subsingleton.elim _ _)))
    exact (isColimitCofanFiberHomologyToPreimageSkeletonZero C R hp q
      ).comp_coconePointUniqueUpToIso_hom _ ⟨k⟩

end ZeroChains

/-! ### The transport along a `1`-cell through its characteristic map -/

section Edge

/-- The Euclidean norm on `ℝ¹` is the absolute value of the coordinate. -/
private lemma norm_euclideanSpace_one (x : EuclideanSpace ℝ (Fin 1)) : ‖x‖ = |x 0| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, Real.sqrt_sq_eq_abs, abs_abs]

/-- In dimension one, the radial rescaling from the Euclidean to the sup-norm unit ball is the
identity on coordinates. -/
private lemma unitBallHomeomorph_one_apply (v : EuclideanSpace ℝ (Fin 1)) :
    (EuclideanSpace.equiv (Fin 1) ℝ).unitBallHomeomorph v = fun _ ↦ v 0 := by
  have hc (x : EuclideanSpace ℝ (Fin 1)) : EuclideanSpace.equiv (Fin 1) ℝ x = fun _ ↦ x 0 :=
    funext fun i ↦ by rw [Subsingleton.elim i 0]; rfl
  have hnorm (x : EuclideanSpace ℝ (Fin 1)) : ‖EuclideanSpace.equiv (Fin 1) ℝ x‖ = ‖x‖ := by
    rw [hc, pi_norm_const, norm_euclideanSpace_one, Real.norm_eq_abs]
  have himage : EuclideanSpace.equiv (Fin 1) ℝ '' closedBall 0 1 = closedBall 0 1 := by
    ext y
    refine ⟨?_, fun hy ↦ ⟨(EuclideanSpace.equiv (Fin 1) ℝ).symm y, ?_,
      (EuclideanSpace.equiv (Fin 1) ℝ).apply_symm_apply y⟩⟩
    · rintro ⟨x, hx, rfl⟩
      rw [mem_closedBall_zero_iff, hnorm]
      exact mem_closedBall_zero_iff.1 hx
    · rw [mem_closedBall_zero_iff, ← hnorm, ContinuousLinearEquiv.apply_symm_apply]
      exact mem_closedBall_zero_iff.1 hy
  rw [ContinuousLinearEquiv.unitBallHomeomorph_apply, himage,
    gaugeRescale_self_apply (absorbent_nhds_zero (closedBall_mem_nhds 0 one_pos))
      (NormedSpace.isVonNBounded_closedBall ℝ _ 1), hc]

variable (j : cell C 1)

/-- The characteristic map of a `1`-cell, as a map from the disk `D¹` to the base. -/
private def cellDiskToBase : C(_root_.TopCat.disk.{u} 1, B) :=
  ⟨fun x ↦ (ConcreteCategory.hom (X := _root_.TopCat.disk.{u} 1)
      (Y := _root_.TopCat.of (skeletonLT C ((1 + 1 : ℕ) : ℕ∞)))
      (TopPair.Hom.fst (characteristicCellPairMap C j)) x).val,
    continuous_subtypeVal.comp (TopPair.Hom.fst (characteristicCellPairMap C j)).hom.continuous⟩

/-- In dimension one, the characteristic map of a cell reads a point of the disk through its
coordinate. -/
private lemma cellDiskToBase_apply (x : _root_.TopCat.disk.{u} 1) :
    cellDiskToBase j x = map 1 j fun _ ↦ (x.down : EuclideanSpace ℝ (Fin 1)) 0 :=
  (coe_characteristicCellPairMap_fst_apply C j x).trans
    (congrArg (map 1 j) (unitBallHomeomorph_one_apply _))

/-- The end point `χⱼ(c)`, `c = ±1`, of a `1`-cell, as a point of the `0`-skeleton. -/
private def cellEnd (c : ℝ) (hc : |c| = 1) : skeletonObj C 1 :=
  ⟨map 1 j fun _ ↦ c, map_mem_skeletonLT_one C j hc⟩

/-- The attaching map of a `1`-cell sends a pole of `S⁰` with coordinate `c` to the end point
`χⱼ(c)`. -/
private lemma characteristicCellPairMap_snd_eq_cellEnd (s : _root_.TopCat.diskBoundary.{u} 1)
    (c : ℝ) (hc : |c| = 1)
    (hs : ((_root_.TopCat.diskBoundaryInclusion 1 s).down : EuclideanSpace ℝ (Fin 1)) 0 = c) :
    TopPair.Hom.snd (characteristicCellPairMap C j) s = cellEnd j c hc :=
  Subtype.ext ((congrArg Subtype.val (TopPair.Hom.w_apply (characteristicCellPairMap C j) s)).trans
    ((cellDiskToBase_apply j _).trans (congrArg (fun a ↦ map 1 j fun _ ↦ a) hs)))

/-- A point of the disk `D¹` is determined by its coordinate. -/
private lemma disk_one_ext {x y : _root_.TopCat.disk.{u} 1}
    (h : (x.down : EuclideanSpace ℝ (Fin 1)) 0 = (y.down : EuclideanSpace ℝ (Fin 1)) 0) : x = y :=
  ULift.ext (Subtype.ext (PiLp.ext fun i ↦ by rw [Subsingleton.elim i 0]; exact h))

/-- The straight path in `D¹` from the pole `-e₀` to the pole `e₀`. -/
private def diskSegment : Path ((diskBoundaryPair.{u} 1).map sphereMinus)
    ((diskBoundaryPair.{u} 1).map spherePlus) where
  toFun t := ULift.up ⟨(EuclideanSpace.equiv (Fin 1) ℝ).symm fun _ ↦ 2 * (t : ℝ) - 1, by
    rw [mem_closedBall_zero_iff, norm_euclideanSpace_one]
    exact unitInterval.abs_two_mul_sub_one_le_one t⟩
  continuous_toFun := by fun_prop
  source' := disk_one_ext ((show (2 * ((0 : unitInterval) : ℝ) - 1) = -1 by norm_num).trans
    sphereMinus_coord.{u}.symm)
  target' := disk_one_ext ((show (2 * ((1 : unitInterval) : ℝ) - 1) = 1 by norm_num).trans
    spherePlus_coord.{u}.symm)

/-- The characteristic map of a `1`-cell sends the pole `-e₀` to the end point `χⱼ(-1)`. -/
private lemma cellDiskToBase_sphereMinus :
    cellDiskToBase j ((diskBoundaryPair.{u} 1).map sphereMinus) = map 1 j fun _ ↦ -1 :=
  (cellDiskToBase_apply j _).trans (congrArg (fun a ↦ map 1 j fun _ ↦ a) sphereMinus_coord)

/-- The characteristic map of a `1`-cell sends the pole `e₀` to the end point `χⱼ(1)`. -/
private lemma cellDiskToBase_spherePlus :
    cellDiskToBase j ((diskBoundaryPair.{u} 1).map spherePlus) = map 1 j fun _ ↦ 1 :=
  (cellDiskToBase_apply j _).trans (congrArg (fun a ↦ map 1 j fun _ ↦ a) spherePlus_coord)

/-- **Through the characteristic map of a `1`-cell, a path class in `D¹` between the poles is the
class of the path of the cell.** Since `D¹` is simply connected, every class from `-e₀` to `e₀`
is the class of the straight segment, which the characteristic map carries to
`TauCeti.cellPath`. -/
private lemma map_cellDiskToBase_eq
    (δ : FundamentalGroupoid.mk ((diskBoundaryPair.{u} 1).map sphereMinus) ⟶
      FundamentalGroupoid.mk ((diskBoundaryPair.{u} 1).map spherePlus)) :
    (FundamentalGroupoid.map (cellDiskToBase j)).map δ =
      eqToHom (congrArg FundamentalGroupoid.mk (cellDiskToBase_sphereMinus j)) ≫
        (Path.Homotopic.Quotient.mk (cellPath C j) :
          FundamentalGroupoid.mk (map 1 j fun _ ↦ -1) ⟶
            FundamentalGroupoid.mk (map 1 j fun _ ↦ 1)) ≫
        eqToHom (congrArg FundamentalGroupoid.mk (cellDiskToBase_spherePlus j).symm) := by
  obtain rfl : δ = Path.Homotopic.Quotient.mk diskSegment :=
    Subsingleton.elim (α := Path.Homotopic.Quotient _ _) _ _
  have hpath : diskSegment.map (cellDiskToBase j).continuous =
      (cellPath C j).cast (cellDiskToBase_sphereMinus j) (cellDiskToBase_spherePlus j) := by
    ext t
    exact (cellDiskToBase_apply j _).trans (cellPath_apply j t).symm
  exact (congrArg Path.Homotopic.Quotient.mk hpath).trans
    (FundamentalGroupoid.conj_eqToHom (p := Path.Homotopic.Quotient.mk (cellPath C j)) _ _).symm

variable (R : Type u) [Ring R] (hp : serreFibrations p) (q : ℕ)

/-- Along the characteristic map of a `1`-cell, the pulled-back local system of fibre homology acts
by the local system of fibre homology of `p` on the image path classes. -/
private lemma map_pullback_characteristicCellPairMap
    {x y : FundamentalGroupoid (_root_.TopCat.disk.{u} 1)} (δ : x ⟶ y) :
    ((LocalCoefficientSystem.pullback (TopPair.Hom.fst (characteristicCellPairMap C j)).hom).obj
        (skeletonSystem C (serreFiberLocalSystemOn C R hp q) (1 + 1))).map δ =
      (serreFiberLocalSystem hp (ModuleCat.of R R) q).map
        ((FundamentalGroupoid.map (cellDiskToBase j)).map δ) := by
  induction δ using Path.Homotopic.Quotient.ind with | mk γ => rfl

/-- A path class in `D¹` from the centre to a point. -/
private def diskPathClass (x : _root_.TopCat.disk.{u} 1) :
    FundamentalGroupoid.mk (diskCenter.{u} 1) ⟶ FundamentalGroupoid.mk x :=
  Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath _ _)

/-- The identification of the fibre of the pulled-back local system at the centre of `D¹` with the
homology of the fibre of `p` over the end point `χⱼ(-1)` of a `1`-cell, by transport along the cell
from the centre to `-e₀`. -/
private def cellCenterToEndIso :
    ((LocalCoefficientSystem.pullback (TopPair.Hom.fst (characteristicCellPairMap C j)).hom).obj
        (skeletonSystem C (serreFiberLocalSystemOn C R hp q) (1 + 1))).obj
          (FundamentalGroupoid.mk (diskCenter.{u} 1)) ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (p.fiber (map 1 j fun _ ↦ -1)) :=
  (serreFiberLocalSystem hp (ModuleCat.of R R) q).mapIso
      ((Groupoid.isoEquivHom _ _).symm
        ((FundamentalGroupoid.map (cellDiskToBase j)).map
            (diskPathClass ((diskBoundaryPair.{u} 1).map sphereMinus)) ≫
          eqToHom (congrArg FundamentalGroupoid.mk (cellDiskToBase_sphereMinus j)))) ≪≫
    serreFiberLocalSystemObjIso hp (ModuleCat.of R R) q _

/-- The forward map of `TauCeti.TopCat.cellCenterToEndIso` is the transport in the base. -/
private lemma cellCenterToEndIso_hom :
    (cellCenterToEndIso j R hp q).hom =
      (serreFiberLocalSystem hp (ModuleCat.of R R) q).map
          ((FundamentalGroupoid.map (cellDiskToBase j)).map
              (diskPathClass ((diskBoundaryPair.{u} 1).map sphereMinus)) ≫
            eqToHom (congrArg FundamentalGroupoid.mk (cellDiskToBase_sphereMinus j))) ≫
        (serreFiberLocalSystemObjIso hp (ModuleCat.of R R) q _).hom :=
  (rfl)

/-- In the fundamental groupoid of the base, transport from the image of the centre of `D¹` to
`χⱼ(-1)`, followed by the path of the cell, is transport from the image of the centre to
`χⱼ(1)`. -/
private lemma map_diskPathClass_comp_cellPath :
    (FundamentalGroupoid.map (cellDiskToBase j)).map
        (diskPathClass ((diskBoundaryPair.{u} 1).map sphereMinus)) ≫
      eqToHom (congrArg FundamentalGroupoid.mk (cellDiskToBase_sphereMinus j)) ≫
        (Path.Homotopic.Quotient.mk (cellPath C j) :
          FundamentalGroupoid.mk (map 1 j fun _ ↦ -1) ⟶
            FundamentalGroupoid.mk (map 1 j fun _ ↦ 1)) =
      (FundamentalGroupoid.map (cellDiskToBase j)).map
          (diskPathClass ((diskBoundaryPair.{u} 1).map spherePlus)) ≫
        eqToHom (congrArg FundamentalGroupoid.mk (cellDiskToBase_spherePlus j)) := by
  -- In the simply connected `D¹`, the class from the centre to `e₀` passes through `-e₀`.
  have hδ : diskPathClass ((diskBoundaryPair.{u} 1).map spherePlus) =
      diskPathClass ((diskBoundaryPair.{u} 1).map sphereMinus) ≫
        Path.Homotopic.Quotient.mk diskSegment :=
    Subsingleton.elim (α := Path.Homotopic.Quotient _ _) _ _
  rw [hδ, Functor.map_comp]
  -- The remaining identity is stated at points of `S⁰` read in `D¹`, which instance-level rewriting
  -- does not see through, so it is assembled by unification.
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine congrArg (_ ≫ ·) (Eq.symm ?_)
  have h := map_cellDiskToBase_eq j (Path.Homotopic.Quotient.mk diskSegment)
  refine (congrArg
    (· ≫ eqToHom (congrArg FundamentalGroupoid.mk (cellDiskToBase_spherePlus j))) h).trans ?_
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) ((eqToHom_trans _ _).trans (eqToHom_refl _ _))).trans (Category.comp_id _))))

omit [T2Space B] in
/-- Transport of fibre homology along a path, read in the local system of fibre homology. -/
private lemma objIso_hom_comp_fiberHomologyTransport_comp {b₀ b₁ : B} (γ : Path b₀ b₁)
    {Z : ModuleCat.{u} R}
    (r : (serreFiberLocalSystem hp (ModuleCat.of R R) q).obj (FundamentalGroupoid.mk b₁) ⟶ Z) :
    (serreFiberLocalSystemObjIso hp (ModuleCat.of R R) q (FundamentalGroupoid.mk b₀)).hom ≫
        fiberHomologyTransport hp (ModuleCat.of R R) q γ ≫
          (serreFiberLocalSystemObjIso hp (ModuleCat.of R R) q
            (FundamentalGroupoid.mk b₁)).inv ≫ r =
      (serreFiberLocalSystem hp (ModuleCat.of R R) q).map (Path.Homotopic.Quotient.mk γ) ≫ r := by
  rw [serreFiberLocalSystem_map_mk]
  simp only [Category.assoc]

/-- **The cellular differential of a `1`-cell with coefficients in the fibre homology is the
transport difference along the cell.** Read through the identification of the fibre at the centre
of the disk with the fibre homology over the end point `χⱼ(-1)`, and through
`Hq(p⁻¹(X⁰), p⁻¹(X⁻¹); R) ≅ H₀(X⁰, X⁻¹; Hq(F))`, the cellular differential of the `1`-cell `j` is
the map `a ↦ a - τⱼ a` of `TauCeti.TopCat.oneCellTransportDifference`. -/
private lemma twistedCellularDifferential_zero_eq :
    (twistedHomologyDiskBoundaryPairIso 1
        ((LocalCoefficientSystem.pullback (TopPair.Hom.fst (characteristicCellPairMap C j)).hom).obj
          (skeletonSystem C (serreFiberLocalSystemOn C R hp q) (1 + 1)))).inv ≫
      TopPair.twistedHomologyMap (characteristicCellPairMap C j)
        (skeletonSystem C (serreFiberLocalSystemOn C R hp q) (1 + 1)) 1 ≫
      twistedCellularDifferential C (serreFiberLocalSystemOn C R hp q) 0 =
    (cellCenterToEndIso j R hp q).hom ≫ Sigma.ι (fun j : cell C 1 ↦
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (p.fiber (map 1 j fun _ ↦ -1))) j ≫
      oneCellTransportDifference C R hp q ≫
      (serreZeroChainsIso C R hp q).hom := by
  -- Both sides are differences of two terms, one for each end point of the cell: the edge formula
  -- of the cellular differential, and `a ↦ a - τⱼ a`. The terms are matched separately, through
  -- the identification of the fibre classes over the end points with their cellular classes.
  rw [twistedHomologyMap_characteristicCellPairMap_comp_twistedCellularDifferential_zero C _ j
    (diskPathClass _) (diskPathClass _), ι_oneCellTransportDifference_assoc, Preadditive.sub_comp,
    Preadditive.comp_sub]
  congr 1
  · refine Eq.trans ?_ (congrArg (_ ≫ ·)
      (fiberHomologyToPreimageSkeletonZero_comp_serreZeroChainsIso_hom
        C R hp q (cellEnd j (-1) (by norm_num)))).symm
    rw [map_pullback_characteristicCellPairMap]
    erw [TopPair.subspaceSystemPullbackIso_hom_app]
    erw [← LocalCoefficientSystem.eqToHom_comp_ιTwistedHomology₀ _
      (characteristicCellPairMap_snd_eq_cellEnd j sphereMinus (-1) (by norm_num) sphereMinus_coord)]
    rw [cellCenterToEndIso_hom, fiberHomologyToTwistedZeroChains]
    -- The fibres are identified only up to unfolding the pulled-back systems, so the two sides
    -- are compared by unification rather than by rewriting.
    refine (congrArg (_ ≫ ·) ((congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans
      (eqToHom_trans_assoc _ _ _))).trans ?_
    refine Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
      (Iso.hom_inv_id_assoc _ _))).symm
    refine Eq.trans ?_ (Functor.map_comp_assoc (serreFiberLocalSystem hp (ModuleCat.of R R) q) _ _
      (LocalCoefficientSystem.ιTwistedHomology₀
          (skeletonSystem C (serreFiberLocalSystemOn C R hp q) 1) (cellEnd j (-1) (by norm_num)) ≫
        (skeletonPair C 0).twistedHomologyπ _ 0)).symm
    erw [eqToHom_map]
    rfl
  · refine Eq.trans ?_ (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
      (fiberHomologyToPreimageSkeletonZero_comp_serreZeroChainsIso_hom
        C R hp q (cellEnd j 1 (by norm_num)))))).symm
    rw [map_pullback_characteristicCellPairMap]
    erw [TopPair.subspaceSystemPullbackIso_hom_app]
    erw [← LocalCoefficientSystem.eqToHom_comp_ιTwistedHomology₀ _
      (characteristicCellPairMap_snd_eq_cellEnd j spherePlus 1 (by norm_num) spherePlus_coord)]
    rw [cellCenterToEndIso_hom, fiberHomologyToTwistedZeroChains]
    symm
    erw [Category.assoc, objIso_hom_comp_fiberHomologyTransport_comp, ← Functor.map_comp_assoc,
      Category.assoc,
      map_diskPathClass_comp_cellPath, Functor.map_comp_assoc, eqToHom_map]
    exact congrArg (_ ≫ ·) ((eqToHom_trans_assoc _ _ _).symm.trans
      (congrArg (_ ≫ ·) (Category.assoc _ _ _).symm))

end Edge

/-! ### The column `p = 0` of the second page -/

section SecondPage

variable (R : Type u) [Ring R] (hp : serreFibrations p)

variable (C) in
/-- The transport differences along the `1`-cells, read in `H₀(X⁰, X⁻¹; Hq(F))`, and the cellular
differential out of the `1`-cells with coefficients in the fibre homology have the same cokernel. -/
private def cokernelOneCellTransportDifferenceIso (q : ℕ) :
    cokernel (oneCellTransportDifference C R hp q ≫
        (serreZeroChainsIso C R hp q).hom) ≅
      cokernel (twistedCellularDifferential.{u, u, u} C (serreFiberLocalSystemOn C R hp q) 0) where
  hom := cokernel.desc _ (cokernel.π _) (Sigma.hom_ext _ _ fun j ↦ by
    have h := (Iso.eq_inv_comp _).2 (twistedCellularDifferential_zero_eq j R hp q).symm
    rw [comp_zero, ← Category.assoc, ← Category.assoc, Category.assoc (Sigma.ι _ j), h]
    simp only [Category.assoc]
    erw [cokernel.condition]
    simp only [comp_zero])
  inv := cokernel.desc _ (cokernel.π _)
    ((isColimitCofanTwistedHomologyMapCharacteristicCellPairMap C
      (serreFiberLocalSystemOn C R hp q) 1).hom_ext fun ⟨j⟩ ↦ by
    have h := (Iso.inv_comp_eq _).1 (twistedCellularDifferential_zero_eq j R hp q)
    have hc := cokernel.condition (oneCellTransportDifference C R hp q ≫
      (serreZeroChainsIso C R hp q).hom)
    rw [Category.assoc] at hc
    simp only [Cofan.mk_pt, Cofan.mk_ι_app, comp_zero]
    rw [← Category.assoc, h]
    simp only [Category.assoc]
    erw [hc]
    simp only [comp_zero])
  hom_inv_id := by rw [← cancel_epi (cokernel.π _)]; simp
  inv_hom_id := by rw [← cancel_epi (cokernel.π _)]; simp

variable (C) in
/-- **The column `p = 0` of the second page of the Serre spectral sequence is cellular homology in
degree zero with coefficients in the fibre homology.** For a Serre fibration `p : E ⟶ B` and a
relative CW complex `C ⊆ B`, the object `E²_{0,q}` of the second page (numbered `3`) of the Serre
spectral sequence, at `pq = (a, b)` with `b = -1` and `a + b = -q`, is the cellular homology
`H₀(C; Hq(F))` of `C` in degree zero, with coefficients in the local system of fibre homology
`b ↦ Hq(p⁻¹(b); R)` with its path-transport monodromy. -/
def serreSpectralSequenceSecondPageXZeroIsoTwistedCellularHomology (q : ℕ) (pq : ℤ × ℤ)
    (hb : pq.2 = -1) (ha : pq.1 + pq.2 = -q) :
    ((serreSpectralSequence C p R).page 3).X pq ≅
      (twistedCellularChainComplex.{u, u, u} C (serreFiberLocalSystemOn C R hp q)).homology 0 :=
  serreSpectralSequenceSecondPageXZeroIsoCokernel C R hp q pq hb ha ≪≫
    (cokernelCompIsIso (serreZeroChainsIso C R hp q).hom _).symm ≪≫
    cokernelOneCellTransportDifferenceIso C R hp q ≪≫
    (twistedCellularChainComplexHomologyZeroIso C (serreFiberLocalSystemOn C R hp q)).symm

variable (C) in
/-- Under `TauCeti.TopCat.serreSpectralSequenceSecondPageXZeroIsoTwistedCellularHomology`, the
projection of the first page onto the second is the identification
`Hq(p⁻¹(X⁰), p⁻¹(X⁻¹); R) ≅ H₀(X⁰, X⁻¹; Hq(F))` of
`TauCeti.TopCat.serreZeroChainsIso`, followed by the projection of the
cellular chains in degree zero onto cellular homology. -/
@[reassoc]
lemma homologyπ_comp_serreSpectralSequenceSecondPageXZeroIsoTwistedCellularHomology_hom (q : ℕ)
    (pq : ℤ × ℤ) (hb : pq.2 = -1) (ha : pq.1 + pq.2 = -q) :
    ((serreSpectralSequence C p R).page 2).homologyπ pq ≫
        ((serreSpectralSequence C p R).iso 2 3 pq rfl le_rfl).hom ≫
        (serreSpectralSequenceSecondPageXZeroIsoTwistedCellularHomology C R hp q pq hb ha).hom =
      ((serreSpectralSequence C p R).page 2).iCycles pq ≫
        (filteredSpaceSpectralSequenceFirstPageXIso (ModuleCat.of R R)
          (monotone_preimageSkeleton p) pq pq.2 (pq.2 + 1) rfl rfl _ rfl q ha).hom ≫
        eqToHom (congrArg (fun P : TopPair.{u} ↦ P.singularHomology (ModuleCat.of R R) q)
          (ofInclusion_preimageSkeleton_eq_preimageSkeletonPair 0 pq.2 (by lia))) ≫
        (serreZeroChainsIso C R hp q).hom ≫
        cokernel.π (twistedCellularDifferential.{u, u, u} C (serreFiberLocalSystemOn C R hp q) 0) ≫
        (twistedCellularChainComplexHomologyZeroIso C (serreFiberLocalSystemOn C R hp q)).inv := by
  rw [serreSpectralSequenceSecondPageXZeroIsoTwistedCellularHomology, Iso.trans_hom, Iso.trans_hom,
    Iso.trans_hom, homologyπ_comp_serreSpectralSequenceSecondPageXZeroIsoCokernel_hom_assoc]
  simp [cokernelOneCellTransportDifferenceIso]

variable (C) in
/-- **The column `p = 0` of the second page of the Serre spectral sequence is the zeroth homology of
the base with coefficients in the fibre homology.** For a Serre fibration `p : E ⟶ B` and a
relative CW complex `C ⊆ B` with base `D`, the object `E²_{0,q}` of the second page (numbered `3`)
of the Serre spectral sequence, at `pq = (a, b)` with `b = -1` and `a + b = -q`, is the relative
singular homology `H₀(C, D; Hq(F))` with coefficients in the local system of fibre homology. -/
def serreSpectralSequenceSecondPageXZeroIsoTwistedHomology (q : ℕ) (pq : ℤ × ℤ)
    (hb : pq.2 = -1) (ha : pq.1 + pq.2 = -q) :
    ((serreSpectralSequence C p R).page 3).X pq ≅
      (complexBasePair C).twistedHomology (serreFiberLocalSystemOn C R hp q) 0 :=
  serreSpectralSequenceSecondPageXZeroIsoTwistedCellularHomology C R hp q pq hb ha ≪≫
    twistedCellularSingularHomologyIso C (serreFiberLocalSystemOn C R hp q) 0

end SecondPage

end TopCat

end TauCeti
