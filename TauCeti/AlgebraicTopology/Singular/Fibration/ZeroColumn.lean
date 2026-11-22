/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Fibration.FirstPage
public import TauCeti.AlgebraicTopology.Singular.Fibration.SerreLocalSystem
public import TauCeti.AlgebraicTopology.Singular.Additivity
import TauCeti.Analysis.Convex.Contractible

/-!
# The column `p = 0` of the second page of the Serre spectral sequence

Let `p : E ⟶ B` be a Serre fibration and `C ⊆ B` a relative CW complex with skeleta `Xⁿ` and base
`X⁻¹`. The first page of the Serre spectral sequence of `p` is the direct sum, over the cells, of
the homology of the fibres over their centres
(`TauCeti.TopCat.serreSpectralSequenceFirstPageXIsoSigma`).
Its column `p = 0` is `E¹_{0,q} = Hq(p⁻¹(X⁰), p⁻¹(X⁻¹); R)`, the fibre homology over the
`0`-cells, and nothing leaves it, so the second page there is the cokernel of the first
differential `d¹ : E¹_{1,q} ⟶ E¹_{0,q}`.

This file identifies that cokernel through path transport. A `1`-cell `j` is a path
`TauCeti.cellPath` from `χⱼ(-1)` to `χⱼ(1)` in the `0`-skeleton, along which the fibre
homology has its transport `τⱼ` (`TauCeti.TopCat.fiberSingularHomologyIsoOfPath`, the
monodromy of the local system of fibre homology `TauCeti.TopCat.serreFiberLocalSystem`). The image
of `d¹` is
spanned by the classes `a - τⱼ a`, for `a` over the end point `χⱼ(-1)`
(`TauCeti.TopCat.oneCellTransportDifference`), so

`E²_{0,q} ≅ Hq(p⁻¹(X⁰), p⁻¹(X⁻¹); R) / ⟨a - τⱼ a⟩`

(`TauCeti.TopCat.serreSpectralSequenceSecondPageXZeroIsoCokernel`), the projection of the first
page to the second being read as the quotient map
(`TauCeti.TopCat.homologyπ_comp_serreSpectralSequenceSecondPageXZeroIsoCokernel_hom`). When `D = ∅`
and `C` is connected, this quotient is classically the module of coinvariants `H₀(C; Hq(F))` of the
fibre homology under the fundamental group; that identification is not proved here.

## The argument

The first differential is the connecting map of the triple `(p⁻¹(X¹), p⁻¹(X⁰), p⁻¹(X⁻¹))`
(`TauCeti.filteredSpaceSpectralSequence_first_page_d_eq`). On the summand of a `1`-cell `j` it is
the connecting map of the pair `(Pⱼ, ∂Pⱼ)` of the pullback of `p` to the closed unit ball of `ℝ¹`
along the characteristic map, followed by the projection of `∂Pⱼ` to `p⁻¹(X⁰)`. The boundary
`∂Pⱼ` is the disjoint union of the fibres over the end points `χⱼ(∓1)`, and the ball is
contractible, so the inclusion `∂Pⱼ ⟶ Pⱼ` is onto in homology. By the exact sequence of the pair,
the image of the connecting map is the kernel of `Hq(∂Pⱼ) ⟶ Hq(Pⱼ)`, and since the two fibre
inclusions into `Pⱼ` differ by the transport `τⱼ`, that kernel is `{(a, -τⱼ a)}`.

## Main definitions and results

* `TauCeti.TopCat.oneCellTransportDifference`: the map `⨁ⱼ Hq(p⁻¹(χⱼ(-1))) ⟶ E¹_{0,q}`,
  `a ↦ a - τⱼ a`.
* `TauCeti.TopCat.serreSpectralSequenceSecondPageXZeroIsoCokernel`: `E²_{0,q}` is its cokernel.
* `TauCeti.TopCat.homologyπ_comp_serreSpectralSequenceSecondPageXZeroIsoCokernel_hom`: under this
  identification, the projection of the first page to the second is the quotient map.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505, Chapter II.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Theorem 5.2 and Section 5.1.
* A. Hatcher,
  [*Spectral Sequences in Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/SSAT/SSch1.pdf),
  Chapter 1, the proof of Theorem 1.3 (the second page with local coefficients).
-/

public section

noncomputable section

open CategoryTheory Limits Metric Set Topology Topology.RelCWComplex

universe u

namespace TauCeti

namespace TopCat

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} [T2Space B] {C D : Set B} [RelCWComplex C D]

section Endpoints

variable (p C) in
/-- The inclusion of the fibre of `p` over a point `b` of the `0`-skeleton into the preimage
`p⁻¹(X⁰)` of the `0`-skeleton. -/
def fiberToPreimageSkeletonZero {b : B} (hb : b ∈ (skeletonLT C ((0 + 1 : ℕ) : ℕ∞) : Set B)) :
    p.fiber b ⟶ (preimageSkeletonPair p C 0).fst :=
  _root_.TopCat.ofHom
    ⟨fun e ↦ ⟨e.val, by rw [mem_preimage, p.apply_coe_fiber b e]; exact hb⟩, by fun_prop⟩

@[simp]
lemma coe_fiberToPreimageSkeletonZero_apply {b : B}
    (hb : b ∈ (skeletonLT C ((0 + 1 : ℕ) : ℕ∞) : Set B)) (e : p.fiber b) :
    (fiberToPreimageSkeletonZero p C hb e).val = e.val :=
  (rfl)

variable (R : Type u) [Ring R]

variable (p C) in
/-- The map `Hq(p⁻¹(b); R) ⟶ Hq(p⁻¹(X⁰), p⁻¹(X⁻¹); R)` induced by the inclusion of the fibre over a
point `b` of the `0`-skeleton. -/
def fiberHomologyToPreimageSkeletonZero (q : ℕ) {b : B}
    (hb : b ∈ (skeletonLT C ((0 + 1 : ℕ) : ℕ∞) : Set B)) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (p.fiber b) ⟶
      (preimageSkeletonPair p C 0).singularHomology (ModuleCat.of R R) q :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).map
      (fiberToPreimageSkeletonZero p C hb) ≫
    (preimageSkeletonPair p C 0).singularHomologyπ (ModuleCat.of R R) q

/-- The map `Hq(p⁻¹(b); R) ⟶ Hq(p⁻¹(X⁰), p⁻¹(X⁻¹); R)` is induced by the inclusion of the fibre,
followed by the quotient map from the absolute to the relative homology. -/
@[reassoc]
lemma fiberHomologyToPreimageSkeletonZero_def (q : ℕ) {b : B}
    (hb : b ∈ (skeletonLT C ((0 + 1 : ℕ) : ℕ∞) : Set B)) :
    fiberHomologyToPreimageSkeletonZero p C R q hb =
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
          (ModuleCat.of R R)).map (fiberToPreimageSkeletonZero p C hb) ≫
        (preimageSkeletonPair p C 0).singularHomologyπ (ModuleCat.of R R) q :=
  (rfl)

variable (hp : serreFibrations p)

variable (C) in
/-- **The transport differences along the `1`-cells.** The map
`⨁ⱼ Hq(p⁻¹(χⱼ(-1)); R) ⟶ Hq(p⁻¹(X⁰), p⁻¹(X⁻¹); R)` which sends a class `a` over the end point
`χⱼ(-1)` of the `1`-cell `j` to `a - τⱼ a`, where `τⱼ` is the transport of fibre homology
(`TauCeti.TopCat.fiberSingularHomologyIsoOfPath`) along the path `TauCeti.cellPath` of `j` to its
other end point `χⱼ(1)`, both classes being read in the homology of `p⁻¹(X⁰)` relative to
`p⁻¹(X⁻¹)`. -/
def oneCellTransportDifference (q : ℕ) :
    (∐ fun j : cell C 1 ↦ ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (p.fiber (map 1 j fun _ ↦ -1))) ⟶
      (preimageSkeletonPair p C 0).singularHomology (ModuleCat.of R R) q :=
  Sigma.desc fun j ↦
    fiberHomologyToPreimageSkeletonZero p C R q (map_mem_skeletonLT_one C j (by norm_num)) -
      (fiberSingularHomologyIsoOfPath hp (ModuleCat.of R R) (cellPath C j) q).hom ≫
        fiberHomologyToPreimageSkeletonZero p C R q (map_mem_skeletonLT_one C j (by norm_num))

/-- On the summand of a `1`-cell `j`, the transport differences send `a` to `a - τⱼ a`. -/
@[reassoc (attr := simp)]
lemma ι_oneCellTransportDifference (q : ℕ) (j : cell C 1) :
    Sigma.ι _ j ≫ oneCellTransportDifference C R hp q =
      fiberHomologyToPreimageSkeletonZero p C R q (map_mem_skeletonLT_one C j (by norm_num)) -
        (fiberSingularHomologyIsoOfPath hp (ModuleCat.of R R) (cellPath C j) q).hom ≫
          fiberHomologyToPreimageSkeletonZero p C R q (map_mem_skeletonLT_one C j (by norm_num)) :=
  Sigma.ι_comp_desc _ _

end Endpoints

section CellBoundary

/-! ### The pullback of `p` along a `1`-cell over the two end points -/

/-- The point `(c)` of the closed unit ball of `ℝ¹`, lifted to the universe `u`. -/
private def ballPoint (c : ℝ) (hc : |c| ≤ 1) : closedBall (0 : ULift.{u} (Fin 1 → ℝ)) 1 :=
  ⟨ULift.up fun _ ↦ c, by
    rw [mem_closedBall_zero_iff, ULift.norm_up, pi_norm_const, Real.norm_eq_abs]
    exact hc⟩

private lemma ballPoint_down (c : ℝ) (hc : |c| ≤ 1) :
    ((ballPoint.{u} c hc : ULift.{u} (Fin 1 → ℝ))).down = fun _ ↦ c :=
  (rfl)

omit [T2Space B] in
private lemma cellULiftMap_ballPoint (j : cell C 1) (c : ℝ) (hc : |c| ≤ 1) :
    cellULiftMap C 1 j (ballPoint c hc) = map 1 j (fun _ ↦ c) :=
  cellULiftMap_apply 1 j _

variable (p) in
/-- The inclusion of the fibre of `p` over the end point `χⱼ(c)`, `c = ±1`, of a `1`-cell `j` into
the part `∂Pⱼ` of the pullback `Pⱼ` of `p` along the characteristic map over the boundary. -/
private def cellBoundaryFiberι (j : cell C 1) (c : ℝ) (hc : |c| = 1) :
    p.fiber (map 1 j fun _ ↦ c) ⟶ (cellDiskPullbackPair p C 1 j).snd :=
  _root_.TopCat.ofHom ⟨fun e ↦ ⟨⟨(ballPoint c hc.le, e.val),
      (cellULiftMap_ballPoint j c hc.le).trans (p.apply_coe_fiber _ e).symm⟩, by
        rw [mem_cellDiskPullbackPair_snd_iff 1 j, mem_sphere_zero_iff_norm, ← ULift.norm_down,
          ballPoint_down, pi_norm_const, Real.norm_eq_abs, hc]⟩,
    by fun_prop⟩

omit [T2Space B] in
/-- The point of the ball under `cellBoundaryFiberι p j c hc` is `ballPoint c`. -/
private lemma cellBoundaryFiberι_apply_ball (j : cell C 1) (c : ℝ) (hc : |c| = 1)
    (e : p.fiber (map 1 j fun _ ↦ c)) :
    (cellBoundaryFiberι p j c hc e).val.val.1 = ballPoint c hc.le :=
  rfl

omit [T2Space B] in
private lemma cellBoundaryFiberι_comp_map (j : cell C 1) (c : ℝ) (hc : |c| = 1) :
    cellBoundaryFiberι p j c hc ≫ (cellDiskPullbackPair p C 1 j).map =
      p.pullbackFiberι (cellULiftMap C 1 j) (cellULiftMap_ballPoint j c hc.le) := by
  ext e : 2
  exact Subtype.ext (TopCat.Hom.coe_pullbackFiberι_apply p (cellULiftMap C 1 j)
    (cellULiftMap_ballPoint j c hc.le) e).symm

private lemma cellBoundaryFiberι_comp_snd (j : cell C 1) (c : ℝ) (hc : |c| = 1) :
    cellBoundaryFiberι p j c hc ≫ TopPair.Hom.snd (cellDiskPullbackPairMap p C 1 j) =
      fiberToPreimageSkeletonZero p C (map_mem_skeletonLT_one C j hc) := by
  ext e : 2
  refine Subtype.ext ?_
  have := TopPair.Hom.w_apply (cellDiskPullbackPairMap p C 1 j) (cellBoundaryFiberι p j c hc e)
  exact (congrArg Subtype.val this).trans (coe_cellDiskPullbackPairMap_fst_apply 1 j _)

variable (R : Type u) [Ring R] (hp : serreFibrations p)

omit [T2Space B] in
/-- Transport of fibre homology along the path of a `1`-cell is transport over the closed unit
ball of `ℝ¹`, along the characteristic map, from `-1` to `1`. -/
private lemma fiberHomologyTransport_cellPath (q : ℕ) (j : cell C 1) :
    (fiberSingularHomologyIsoOfPath hp (ModuleCat.of R R) (cellPath C j) q).hom =
      (pullbackFiberIso (weakEquivalences_isInvertedBy_singularHomologyFunctor (ModuleCat.of R R) q)
        hp (cellULiftMap C 1 j)
        (cellULiftMap_ballPoint j (-1) (by norm_num))
        (cellULiftMap_ballPoint j 1 (by norm_num))).hom := by
  dsimp only [fiberSingularHomologyIsoOfPath]
  rw [fiberIsoOfPath_eq_pullbackFiberIso]
  -- The interval `I` maps to the ball by `t ↦ 2t - 1`, over `B`.
  let φ : _root_.TopCat.I.{u} ⟶ _root_.TopCat.of (closedBall (0 : ULift.{u} (Fin 1 → ℝ)) 1) :=
    _root_.TopCat.ofHom ⟨fun t ↦ ballPoint (2 * (_root_.TopCat.I.homeomorph t : ℝ) - 1)
      (unitInterval.abs_two_mul_sub_one_le_one _), by
      unfold ballPoint
      fun_prop⟩
  refine congrArg Iso.hom
    (pullbackFiberIso_comp_left _ hp _ _ φ ?_ (k₀ := 0) (k₁ := 1) ?_ ?_ _ _ _ _)
  · ext t
    simp only [ConcreteCategory.comp_apply]
    rw [TopCat.pathEquiv_symm_hom_apply, cellPath_apply]
    exact cellULiftMap_ballPoint j _ (unitInterval.abs_two_mul_sub_one_le_one _)
  · refine Subtype.ext (congrArg ULift.up (funext fun _ ↦ ?_))
    simp
  · refine Subtype.ext (congrArg ULift.up (funext fun _ ↦ ?_))
    norm_num

/-! ### The two ends of the boundary of a `1`-cell -/

omit [T2Space B] in
/-- A point of the boundary sphere of the closed unit ball of `ℝ¹` is `-1` or `1`. -/
private lemma abs_down_eq_one (j : cell C 1) (x : (cellDiskPullbackPair p C 1 j).snd) :
    |(x.val.val.1 : ULift.{u} (Fin 1 → ℝ)).down 0| = 1 := by
  have hx : ‖(x.val.val.1 : ULift.{u} (Fin 1 → ℝ))‖ = 1 := mem_sphere_zero_iff_norm.1
    ((mem_cellDiskPullbackPair_snd_iff 1 j x.val).1 x.property)
  have hv : (x.val.val.1 : ULift.{u} (Fin 1 → ℝ)).down =
      fun _ ↦ (x.val.val.1 : ULift.{u} (Fin 1 → ℝ)).down 0 :=
    funext fun i ↦ by rw [Subsingleton.elim i 0]
  rwa [← ULift.norm_down, hv, pi_norm_const, Real.norm_eq_abs] at hx

variable (p) in
/-- The part of the boundary `∂Pⱼ` of the pullback along a `1`-cell `j` over the end point `c`,
for `c = ±1`, as an open set. -/
private def cellBoundaryOpens (j : cell C 1) (c : ℝ) :
    TopologicalSpace.Opens (cellDiskPullbackPair p C 1 j).snd :=
  ⟨{x | 0 < c * (x.val.val.1 : ULift.{u} (Fin 1 → ℝ)).down 0},
    isOpen_lt continuous_const (by fun_prop)⟩

omit [T2Space B] in
private lemma mem_cellBoundaryOpens (j : cell C 1) (c : ℝ)
    (x : (cellDiskPullbackPair p C 1 j).snd) :
    x ∈ cellBoundaryOpens p j c ↔ 0 < c * (x.val.val.1 : ULift.{u} (Fin 1 → ℝ)).down 0 :=
  Iff.rfl

omit [T2Space B] in
private lemma ballPoint_eq_of_mem_cellBoundaryOpens (j : cell C 1) {c : ℝ} (hc : |c| = 1)
    {x : (cellDiskPullbackPair p C 1 j).snd} (hx : x ∈ cellBoundaryOpens p j c) :
    x.val.val.1 = ballPoint c hc.le := by
  -- Both `c` and the coordinate of `x` are `±1`, with positive product.
  have h : (x.val.val.1 : ULift.{u} (Fin 1 → ℝ)).down 0 = c := by
    have hx' := (mem_cellBoundaryOpens j c x).1 hx
    rcases abs_eq zero_le_one |>.1 hc with rfl | rfl <;>
      rcases abs_eq zero_le_one |>.1 (abs_down_eq_one j x) with h | h <;> rw [h] at hx' ⊢ <;>
      linarith
  refine Subtype.ext (congrArg ULift.up (funext fun i ↦ ?_))
  rw [Subsingleton.elim i 0]
  exact h

variable (p) in
/-- The fibre of `p` over the end point `χⱼ(c)` of a `1`-cell is the part of `∂Pⱼ` over `c`. -/
private def cellBoundaryOpensHomeomorph (j : cell C 1) (c : ℝ) (hc : |c| = 1) :
    p.fiber (map 1 j fun _ ↦ c) ≃ₜ cellBoundaryOpens p j c where
  toFun e := ⟨cellBoundaryFiberι p j c hc e, by
    -- The point of the ball under `cellBoundaryFiberι` is `c`.
    rw [mem_cellBoundaryOpens, cellBoundaryFiberι_apply_ball, ballPoint_down]
    nlinarith [abs_mul_abs_self c, hc]⟩
  invFun x := ⟨x.val.val.val.2, by
    have h := x.val.val.property
    rw [ballPoint_eq_of_mem_cellBoundaryOpens j hc x.property, cellULiftMap_ballPoint] at h
    exact h.symm⟩
  left_inv _ := rfl
  right_inv x := Subtype.ext <| Subtype.ext <| Subtype.ext <|
    Prod.ext (ballPoint_eq_of_mem_cellBoundaryOpens j hc x.property).symm rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

omit [T2Space B] in
/-- **Morphisms out of the homology of the boundary of a `1`-cell are determined on the two end
fibres.** The boundary `∂Pⱼ` is the disjoint union of the fibres over `χⱼ(-1)` and `χⱼ(1)`. -/
private lemma cellBoundary_hom_ext (q : ℕ) (j : cell C 1) {Z : ModuleCat.{u} R}
    {f f' : ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
      (ModuleCat.of R R)).obj (cellDiskPullbackPair p C 1 j).snd ⟶ Z}
    (hneg : ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).map (cellBoundaryFiberι p j (-1) (by norm_num)) ≫ f =
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).map (cellBoundaryFiberι p j (-1) (by norm_num)) ≫ f')
    (hpos : ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).map (cellBoundaryFiberι p j 1 (by norm_num)) ≫ f =
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).map (cellBoundaryFiberι p j 1 (by norm_num)) ≫ f') :
    f = f' := by
  let H := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)
  let c : ULift.{u} Bool → ℝ := fun i ↦ bif i.down then -1 else 1
  have hc (i : ULift.{u} Bool) : |c i| = 1 := by
    rcases i with ⟨_ | _⟩ <;> norm_num [c]
  let s : ULift.{u} Bool → TopologicalSpace.Opens (cellDiskPullbackPair p C 1 j).snd :=
    fun i ↦ cellBoundaryOpens p j (c i)
  have hs : Pairwise (Function.onFun Disjoint s) := by
    rintro ⟨_ | _⟩ ⟨_ | _⟩ h
    all_goals first
      | exact absurd rfl h
      | exact TopologicalSpace.Opens.coe_disjoint.1 <| Set.disjoint_left.2 fun x hx hx' ↦ by
          simp only [s, SetLike.mem_coe, mem_cellBoundaryOpens, c, Bool.cond_true,
            Bool.cond_false] at hx hx'
          linarith
  -- The two ends cover the boundary, so the inclusion of their union is a homeomorphism.
  have hcov (x : (cellDiskPullbackPair p C 1 j).snd) : x ∈ ⨆ i, s i := by
    rw [TopologicalSpace.Opens.mem_iSup]
    rcases abs_eq zero_le_one |>.1 (abs_down_eq_one j x) with h | h
    · exact ⟨⟨false⟩, (mem_cellBoundaryOpens j _ x).2 (by simp [c, h])⟩
    · exact ⟨⟨true⟩, (mem_cellBoundaryOpens j _ x).2 (by simp [c, h])⟩
  let val : _root_.TopCat.of ↥(⨆ i, s i) ⟶ (cellDiskPullbackPair p C 1 j).snd :=
    _root_.TopCat.ofHom ⟨Subtype.val, continuous_subtypeVal⟩
  have : IsIso val := (_root_.TopCat.isIso_iff_isHomeomorph _).2
    (isHomeomorph_iff_isEmbedding_surjective.2
      ⟨IsEmbedding.subtypeVal, fun x ↦ ⟨⟨x, hcov x⟩, rfl⟩⟩)
  rw [← cancel_epi (H.map val)]
  refine (isColimitCofanSingularHomologyOpens s (ModuleCat.{u} R) (ModuleCat.of R R) q
    hs).hom_ext fun ⟨i⟩ ↦ ?_
  -- On the part over each end point, read through the fibre over that end point, the leg is the
  -- fibre inclusion into `∂Pⱼ`.
  let e := cellBoundaryOpensHomeomorph p j (c i) (hc i)
  have hleg : (_root_.TopCat.isoOfHomeo e).hom ≫ _root_.TopCat.ofHom
      ⟨TopologicalSpace.Opens.inclusion (le_iSup s i), continuous_inclusion _⟩ ≫ val =
      cellBoundaryFiberι p j (c i) (hc i) :=
    rfl
  refine (cancel_epi (H.map (_root_.TopCat.isoOfHomeo e).hom)).1 ?_
  have hmap := congrArg H.map hleg
  rw [Functor.map_comp, Functor.map_comp] at hmap
  -- The leg of the cofan and `hmap` agree up to unfolding the cofan and the objects `s i`.
  refine ((reassoc_of% hmap) f).trans (Eq.trans ?_ ((reassoc_of% hmap) f').symm)
  rcases i with _ | _
  · exact hpos
  · exact hneg

end CellBoundary

section SecondPage

variable (R : Type u) [Ring R] (hp : serreFibrations p)

variable (p C) in
/-- The triple `(p⁻¹(X¹), p⁻¹(X⁰), p⁻¹(X⁻¹))` of the first three stages of the skeletal
filtration. -/
private abbrev skeletonTriple : TopTriple.{u} :=
  TopTriple.ofInclusions (preimage_mono (f := p) (skeletonLT_subset_skeletonLT_succ C 0))
    (preimage_mono (f := p) (skeletonLT_subset_skeletonLT_succ C 1))

variable (p C) in
/-- The connecting map `Hq+1(p⁻¹(X¹), p⁻¹(X⁰)) ⟶ Hq(p⁻¹(X⁰), p⁻¹(X⁻¹))` of the triple of the first
three stages of the skeletal filtration. -/
private def skeletonδ (q : ℕ) :
    (preimageSkeletonPair p C 1).singularHomology (ModuleCat.of R R) (q + 1) ⟶
      (preimageSkeletonPair p C 0).singularHomology (ModuleCat.of R R) q :=
  (skeletonTriple p C).singularHomologyδ (ModuleCat.of R R) (q + 1) q

omit [T2Space B] in
/-- The fibre inclusions into the pullback `Pⱼ` at the two ends of a `1`-cell differ by the
transport along its path. -/
private lemma map_pullbackFiberι_neg (q : ℕ) (j : cell C 1) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).map
        (p.pullbackFiberι (cellULiftMap C 1 j) (cellULiftMap_ballPoint j (-1) (by norm_num))) =
      (fiberSingularHomologyIsoOfPath hp (ModuleCat.of R R) (cellPath C j) q).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
          (ModuleCat.of R R)).map
            (p.pullbackFiberι (cellULiftMap C 1 j) (cellULiftMap_ballPoint j 1 (by norm_num))) := by
  rw [fiberHomologyTransport_cellPath, pullbackFiberIso_hom_comp_map_pullbackFiberι]

omit [T2Space B] in
/-- The isomorphism `Hq(p⁻¹(χⱼ(1))) ≅ Hq(Pⱼ)` induced by the inclusion of the fibre over the end
point `1` into the pullback along the contractible ball, through its boundary `∂Pⱼ`. -/
private def pullbackFiberιIso (q : ℕ) (j : cell C 1) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).obj
        (p.fiber (map 1 j fun _ ↦ 1)) ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).obj
        (cellDiskPullbackPair p C 1 j).fst :=
  haveI : IsIso (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
      (ModuleCat.of R R)).map (cellBoundaryFiberι p j 1 abs_one ≫
        (cellDiskPullbackPair p C 1 j).map)) := by
    rw [cellBoundaryFiberι_comp_map]
    exact isIso_map_pullbackFiberι
      (weakEquivalences_isInvertedBy_singularHomologyFunctor (ModuleCat.of R R) q) hp
      (cellULiftMap C 1 j) _
  asIso (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
    (ModuleCat.of R R)).map (cellBoundaryFiberι p j 1 abs_one ≫ (cellDiskPullbackPair p C 1 j).map))

variable (p) in
/-- The connecting map `Hq+1(Pⱼ, ∂Pⱼ) ⟶ Hq(∂Pⱼ)` of the pair over a `1`-cell `j`. -/
private def cellBoundaryδ (q : ℕ) (j : cell C 1) :
    (cellDiskPullbackPair p C 1 j).singularHomology (ModuleCat.of R R) (q + 1) ⟶
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (cellDiskPullbackPair p C 1 j).snd :=
  (cellDiskPullbackPair p C 1 j).singularHomologyδ (ModuleCat.of R R) (q + 1) q

variable (p) in
/-- The map `Hq(∂Pⱼ) ⟶ Hq(p⁻¹(X⁰), p⁻¹(X⁻¹))` induced by the projection of the boundary of the
pullback over a `1`-cell `j`. -/
private def cellBoundaryProj (q : ℕ) (j : cell C 1) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (cellDiskPullbackPair p C 1 j).snd ⟶
      (preimageSkeletonPair p C 0).singularHomology (ModuleCat.of R R) q :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
      (ModuleCat.of R R)).map (TopPair.Hom.snd (cellDiskPullbackPairMap p C 1 j)) ≫
    (preimageSkeletonPair p C 0).singularHomologyπ (ModuleCat.of R R) q

variable (p) in
/-- The map `Hq(∂Pⱼ) ⟶ Hq(Pⱼ)` induced by the inclusion of the boundary of the pullback over a
`1`-cell `j`. -/
private def cellBoundaryIncl (q : ℕ) (j : cell C 1) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (cellDiskPullbackPair p C 1 j).snd ⟶
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (cellDiskPullbackPair p C 1 j).fst :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
      (ModuleCat.of R R)).map (cellDiskPullbackPair p C 1 j).map

/-- On the summand of a `1`-cell `j`, the connecting map of the triple of the first stages of the
skeletal filtration is the connecting map of the pair `(Pⱼ, ∂Pⱼ)`, followed by the projection of
`∂Pⱼ` to `p⁻¹(X⁰)`. -/
@[reassoc]
private lemma singularHomologyMap_cellDiskPullbackPairMap_comp_δ (q : ℕ) (j : cell C 1) :
    (cellDiskPullbackPair p C 1 j).singularHomologyMap (cellDiskPullbackPairMap p C 1 j)
        (ModuleCat.of R R) (q + 1) ≫ skeletonδ p C R q =
      cellBoundaryδ p R q j ≫ cellBoundaryProj p R q j := by
  have h₁ := (skeletonTriple p C).singularHomologyδ_eq_comp_singularHomologyπ (ModuleCat.of R R)
    (q + 1) q
  have h₂ := TopPair.singularHomologyδ_naturality (R := ModuleCat.of R R)
    (cellDiskPullbackPairMap p C 1 j) (q + 1) q
  refine (congrArg (_ ≫ ·) (h₁ : skeletonδ p C R q = _)).trans ?_
  exact ((Category.assoc _ _ _).symm.trans (h₂ =≫ _).symm).trans (Category.assoc _ _ _)

omit [T2Space B] in
@[reassoc (attr := simp)]
private lemma cellBoundaryδ_comp_cellBoundaryIncl (q : ℕ) (j : cell C 1) :
    cellBoundaryδ p R q j ≫ cellBoundaryIncl p R q j = 0 :=
  (cellDiskPullbackPair p C 1 j).singularHomologyδ_comp (ModuleCat.of R R) (q + 1) q

omit [T2Space B] in
private lemma exact_cellBoundaryδ (q : ℕ) (j : cell C 1) :
    (ShortComplex.mk _ _ (cellBoundaryδ_comp_cellBoundaryIncl (p := p) R q j)).Exact :=
  (cellDiskPullbackPair p C 1 j).singularHomology_exact_subspace (ModuleCat.of R R) (q + 1) q

/-- The fibre inclusions at the two ends of `∂Pⱼ`, followed by the projection to `p⁻¹(X⁰)`. -/
@[reassoc]
private lemma map_cellBoundaryFiberι_comp_cellBoundaryProj (q : ℕ) (j : cell C 1) (c : ℝ)
    (hc : |c| = 1) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).map (cellBoundaryFiberι p j c hc) ≫ cellBoundaryProj p R q j =
      fiberHomologyToPreimageSkeletonZero p C R q (map_mem_skeletonLT_one C j hc) := by
  rw [cellBoundaryProj, fiberHomologyToPreimageSkeletonZero_def, ← cellBoundaryFiberι_comp_snd]
  exact (Functor.map_comp_assoc _ _ _ _).symm

omit [T2Space B] in
/-- Through the boundary `∂Pⱼ`, the fibre inclusion at the end point `1` is the isomorphism
`Hq(p⁻¹(χⱼ(1))) ≅ Hq(Pⱼ)`. -/
@[reassoc]
private lemma map_cellBoundaryFiberι_one_comp_cellBoundaryIncl (q : ℕ) (j : cell C 1) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).map (cellBoundaryFiberι p j 1 (by norm_num)) ≫
      cellBoundaryIncl p R q j = (pullbackFiberιIso R hp q j).hom := by
  rw [cellBoundaryIncl, ← Functor.map_comp, pullbackFiberιIso, asIso_hom]

omit [T2Space B] in
/-- Through the boundary `∂Pⱼ`, the fibre inclusions at the two end points differ by the transport
along the path of the cell. -/
@[reassoc]
private lemma map_cellBoundaryFiberι_neg_one_comp_cellBoundaryIncl (q : ℕ) (j : cell C 1) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).map (cellBoundaryFiberι p j (-1) (by norm_num)) ≫
      cellBoundaryIncl p R q j =
      (fiberSingularHomologyIsoOfPath hp (ModuleCat.of R R) (cellPath C j) q).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
          (ModuleCat.of R R)).map (cellBoundaryFiberι p j 1 (by norm_num)) ≫
        cellBoundaryIncl p R q j := by
  rw [cellBoundaryIncl, ← Functor.map_comp, ← Functor.map_comp, cellBoundaryFiberι_comp_map,
    cellBoundaryFiberι_comp_map]
  exact map_pullbackFiberι_neg R hp q j

/-- **The first differential out of the `1`-cells lands in the transport relations.** -/
private lemma δ_comp_cokernel_π (q : ℕ) :
    skeletonδ p C R q ≫ cokernel.π (oneCellTransportDifference C R hp q) = 0 := by
  refine (isColimitCofanSingularHomologyPreimageSkeletonPair C hp R 1 (q + 1)).hom_ext
    fun ⟨j⟩ ↦ ?_
  simp only [Cofan.mk_ι_app, comp_zero]
  rw [singularHomologyMap_cellDiskPullbackPairMap_comp_δ_assoc]
  -- The projection of `∂Pⱼ` to the cokernel factors through the homology of `Pⱼ`.
  have hfac : cellBoundaryProj p R q j ≫ cokernel.π (oneCellTransportDifference C R hp q) =
      cellBoundaryIncl p R q j ≫ (pullbackFiberιIso R hp q j).inv ≫
        fiberHomologyToPreimageSkeletonZero p C R q (map_mem_skeletonLT_one C j (by norm_num)) ≫
          cokernel.π (oneCellTransportDifference C R hp q) := by
    have hT := Sigma.ι _ j ≫= cokernel.condition (oneCellTransportDifference C R hp q)
    rw [ι_oneCellTransportDifference_assoc, comp_zero, Preadditive.sub_comp, sub_eq_zero,
      Category.assoc] at hT
    refine cellBoundary_hom_ext R q j ?_ ?_
    · rw [map_cellBoundaryFiberι_comp_cellBoundaryProj_assoc, hT,
        map_cellBoundaryFiberι_neg_one_comp_cellBoundaryIncl_assoc R hp,
        map_cellBoundaryFiberι_one_comp_cellBoundaryIncl_assoc R hp, Iso.hom_inv_id_assoc]
    · rw [map_cellBoundaryFiberι_comp_cellBoundaryProj_assoc,
        map_cellBoundaryFiberι_one_comp_cellBoundaryIncl_assoc R hp, Iso.hom_inv_id_assoc]
  rw [hfac, cellBoundaryδ_comp_cellBoundaryIncl_assoc, zero_comp]

/-- **The transport relations are boundaries of the first differential.** -/
private lemma oneCellTransportDifference_comp_cokernel_π (q : ℕ) :
    oneCellTransportDifference C R hp q ≫ cokernel.π (skeletonδ p C R q) = 0 := by
  refine Sigma.hom_ext _ _ fun j ↦ ?_
  rw [ι_oneCellTransportDifference_assoc, comp_zero, Preadditive.sub_comp, sub_eq_zero,
    Category.assoc]
  -- The projection of `∂Pⱼ` to the cokernel kills the boundaries of `(Pⱼ, ∂Pⱼ)`, and the
  -- homology of `∂Pⱼ` maps onto that of `Pⱼ`, with cokernel those boundaries.
  have hzero := (cellDiskPullbackPair p C 1 j).singularHomologyMap
    (cellDiskPullbackPairMap p C 1 j) (ModuleCat.of R R) (q + 1) ≫=
      cokernel.condition (skeletonδ p C R q)
  rw [comp_zero, singularHomologyMap_cellDiskPullbackPairMap_comp_δ_assoc] at hzero
  have : Epi (cellBoundaryIncl p R q j) :=
    epi_of_epi_fac (f := (pullbackFiberιIso R hp q j).inv ≫
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).map (cellBoundaryFiberι p j 1 (by norm_num)))
      (by rw [Category.assoc, map_cellBoundaryFiberι_one_comp_cellBoundaryIncl R hp,
        Iso.inv_hom_id])
  obtain ⟨χ, hχ⟩ :=
    CokernelCofork.IsColimit.desc' (exact_cellBoundaryδ (p := p) R q j).gIsCokernel _ hzero
  rw [← map_cellBoundaryFiberι_comp_cellBoundaryProj_assoc R q j (-1) (by norm_num),
    ← map_cellBoundaryFiberι_comp_cellBoundaryProj_assoc R q j 1 (by norm_num), ← hχ]
  exact map_cellBoundaryFiberι_neg_one_comp_cellBoundaryIncl_assoc R hp q j χ

variable (C) in
/-- The cokernel of the connecting map `Hq+1(p⁻¹(X¹), p⁻¹(X⁰)) ⟶ Hq(p⁻¹(X⁰), p⁻¹(X⁻¹))` of the
first stages of the skeletal filtration is the cokernel of the transport differences along the
`1`-cells. -/
private def cokernelSkeletonTripleδIso (q : ℕ) :
    cokernel (skeletonδ p C R q) ≅
      cokernel (oneCellTransportDifference C R hp q) where
  hom := cokernel.desc _ _ (δ_comp_cokernel_π R hp q)
  inv := cokernel.desc _ _ (oneCellTransportDifference_comp_cokernel_π R hp q)
  hom_inv_id := by rw [← cancel_epi (cokernel.π _)]; simp
  inv_hom_id := by rw [← cancel_epi (cokernel.π _)]; simp

/-- The comparison `TauCeti.TopCat.cokernelSkeletonTripleδIso` for any triple of subsets equal to
the first three stages of the skeletal filtration. -/
private def cokernelTripleδIsoOfEq {s t w : Set E} (h₁ : s ⊆ t) (h₂ : t ⊆ w)
    (hs : s = p ⁻¹' (skeletonLT C ((0 : ℕ) : ℕ∞) : Set B))
    (ht : t = p ⁻¹' (skeletonLT C ((0 + 1 : ℕ) : ℕ∞) : Set B))
    (hw : w = p ⁻¹' (skeletonLT C ((1 + 1 : ℕ) : ℕ∞) : Set B)) (q : ℕ) :
    cokernel ((TopTriple.ofInclusions h₁ h₂).singularHomologyδ (ModuleCat.of R R) (q + 1) q) ≅
      cokernel (oneCellTransportDifference C R hp q) := by
  subst hs ht hw
  exact cokernelSkeletonTripleδIso C R hp q

/-- On the quotient map, `TauCeti.TopCat.cokernelTripleδIsoOfEq` is the quotient map by the
transport differences. -/
private lemma π_comp_cokernelTripleδIsoOfEq_hom {s t w : Set E} (h₁ : s ⊆ t) (h₂ : t ⊆ w)
    (hs : s = p ⁻¹' (skeletonLT C ((0 : ℕ) : ℕ∞) : Set B))
    (ht : t = p ⁻¹' (skeletonLT C ((0 + 1 : ℕ) : ℕ∞) : Set B))
    (hw : w = p ⁻¹' (skeletonLT C ((1 + 1 : ℕ) : ℕ∞) : Set B)) (q : ℕ) :
    cokernel.π _ ≫ (cokernelTripleδIsoOfEq R hp h₁ h₂ hs ht hw q).hom =
      eqToHom (congrArg (fun P : TopPair.{u} ↦ P.singularHomology (ModuleCat.of R R) q)
          (show TopPair.ofInclusion h₁ = preimageSkeletonPair p C 0 by
            -- After substitution both sides are `ofInclusion` of the same two sets: the
            -- abbreviation `preimageSkeletonPair p C 0` is that pair, and the two inclusion
            -- proofs agree by proof irrelevance.
            subst hs ht; rfl)) ≫
        cokernel.π (oneCellTransportDifference C R hp q) := by
  subst hs ht hw
  simp only [cokernelTripleδIsoOfEq, cokernelSkeletonTripleδIso, eqToHom_refl, Category.id_comp]
  exact cokernel.π_desc _ _ _

variable (C) in
/-- The homology of the first page at a point of the column `p = 0` is the cokernel of the
transport differences along the `1`-cells. -/
private def homologyIsoCokernel (q : ℕ) (pq : ℤ × ℤ) (hb : pq.2 = -1) (ha : pq.1 + pq.2 = -q) :
    ((serreSpectralSequence C p R).page 2 le_rfl).homology pq ≅
      cokernel (oneCellTransportDifference C R hp q) :=
  eqToIso (congrArg (fun pq ↦ ((serreSpectralSequence C p R).page 2 le_rfl).homology pq)
      (Prod.ext (by dsimp only; lia) (by dsimp only; lia) : pq = (-1 - (q : ℤ) + 2, 0 - 1))) ≪≫
    ((serreSpectralSequence C p R).page 2 le_rfl).isoHomologyι _ (-1 - (q : ℤ) + 2 + 2, 0 - 1 - 1)
      (ComplexShape.next_eq' _ (Prod.ext (by simp only [Prod.fst_add])
        (by simp only [Prod.snd_add]; lia)))
      ((isZero_serreSpectralSequence_page_two_X_of_snd_le_neg_two R C _
        (by dsimp only; lia)).eq_of_tgt _ _) ≪≫
    (((serreSpectralSequence C p R).page 2 le_rfl).opcyclesIsCokernel (-1 - (q : ℤ), 0) _
      (ComplexShape.prev_eq' _ (Prod.ext (by simp only [Prod.fst_add])
        (by simp only [Prod.snd_add]; lia)))).coconePointUniqueUpToIso (cokernelIsCokernel _) ≪≫
    cokernelIsoOfEq (filteredSpaceSpectralSequence_first_page_d_eq (ModuleCat.of R R)
      (monotone_preimageSkeleton p) 0 (-1 - q) q (by lia)) ≪≫
    -- The first differential reaches these isomorphisms only up to unfolding its intermediate
    -- objects, so the square is closed by unification rather than by `simp`.
    cokernel.mapIso _ _
      (filteredSpaceSpectralSequenceFirstPageXIso (ModuleCat.of R R) (monotone_preimageSkeleton p)
        (-1 - (q : ℤ), 0) 0 (0 + 1) rfl rfl (-1 - q + 0) rfl (q + 1) (by lia))
      (filteredSpaceSpectralSequenceFirstPageXIso (ModuleCat.of R R) (monotone_preimageSkeleton p)
        (-1 - (q : ℤ) + 2, 0 - 1) (0 - 1) 0 rfl (by lia) (-1 - q + 0 + 1) (by lia) q (by lia))
      ((Iso.eq_comp_inv _).1 (Category.assoc _ _ _).symm) ≪≫
    cokernelTripleδIsoOfEq R hp _ _
      (by rw [preimageSkeleton_def, show ((0 : ℤ) - 1 + 1).toNat = 0 by lia])
      (by rw [preimageSkeleton_def, show ((0 : ℤ) + 1).toNat = 0 + 1 by lia])
      (by rw [preimageSkeleton_def, show ((0 : ℤ) + 1 + 1).toNat = 1 + 1 by lia]) q

variable (C) in
/-- **The column `p = 0` of the second page of the Serre spectral sequence.** For a Serre
fibration `p : E ⟶ B` and a relative CW complex `C ⊆ B` with skeleta `Xⁿ`, the object `E²_{0,q}` of
the second page (numbered `3`) of the Serre spectral sequence, at `pq = (a, b)` with `b = -1` and
`a + b = -q`, is the quotient of `Hq(p⁻¹(X⁰), p⁻¹(X⁻¹); R)`, the fibre homology over the
`0`-skeleton, by the classes `a - τⱼ a` of the transport differences along the `1`-cells
(`TauCeti.TopCat.oneCellTransportDifference`): it is the cokernel of the first differential, which
has the same image as the transport differences. -/
def serreSpectralSequenceSecondPageXZeroIsoCokernel (q : ℕ) (pq : ℤ × ℤ) (hb : pq.2 = -1)
    (ha : pq.1 + pq.2 = -q) :
    ((serreSpectralSequence C p R).page 3).X pq ≅ cokernel (oneCellTransportDifference C R hp q) :=
  ((serreSpectralSequence C p R).iso 2 3 pq rfl le_rfl).symm ≪≫
    homologyIsoCokernel C R hp q pq hb ha

/-- The first-page identification, read in a fixed pair, does not depend on how the upper stage
and the total degree are written. -/
private lemma filteredSpaceSpectralSequenceFirstPageXIso_hom_comp_eqToHom {pq : ℤ × ℤ}
    {a b b' m m' : ℤ} (ha : a = pq.2) (hb : b = pq.2 + 1) (hb' : b' = pq.2 + 1)
    (hm : m = pq.1 + pq.2) (hm' : m' = pq.1 + pq.2) {n : ℕ} (hn : m = -n) (hn' : m' = -n)
    {P : TopPair.{u}}
    (h : TopPair.ofInclusion (monotone_preimageSkeleton (C := C) p (by lia : a ≤ b)) = P)
    (h' : TopPair.ofInclusion (monotone_preimageSkeleton (C := C) p (by lia : a ≤ b')) = P) :
    (filteredSpaceSpectralSequenceFirstPageXIso (ModuleCat.of R R) (monotone_preimageSkeleton p)
        pq a b ha hb m hm n hn).hom ≫
        eqToHom (congrArg (fun P : TopPair.{u} ↦ P.singularHomology (ModuleCat.of R R) n) h) =
      (filteredSpaceSpectralSequenceFirstPageXIso (ModuleCat.of R R) (monotone_preimageSkeleton p)
        pq a b' ha hb' m' hm' n hn').hom ≫
        eqToHom (congrArg (fun P : TopPair.{u} ↦ P.singularHomology (ModuleCat.of R R) n) h') := by
  subst hb hb' hm hm'
  rfl

variable (C) in
/-- On the cycles, `TauCeti.TopCat.homologyIsoCokernel` is the quotient map by the transport
differences. -/
private lemma homologyπ_comp_homologyIsoCokernel_hom (q : ℕ) (pq : ℤ × ℤ) (hb : pq.2 = -1)
    (ha : pq.1 + pq.2 = -q) :
    ((serreSpectralSequence C p R).page 2).homologyπ pq ≫
        (homologyIsoCokernel C R hp q pq hb ha).hom =
      ((serreSpectralSequence C p R).page 2).iCycles pq ≫
        (filteredSpaceSpectralSequenceFirstPageXIso (ModuleCat.of R R)
          (monotone_preimageSkeleton p) pq pq.2 (pq.2 + 1) rfl rfl _ rfl q ha).hom ≫
        eqToHom (congrArg (fun P : TopPair.{u} ↦ P.singularHomology (ModuleCat.of R R) q)
          (ofInclusion_preimageSkeleton_eq_preimageSkeletonPair 0 pq.2 (by lia))) ≫
        cokernel.π (oneCellTransportDifference C R hp q) := by
  obtain rfl : pq = (-1 - (q : ℤ) + 2, 0 - 1) := Prod.ext (by lia) (by lia)
  simp only [homologyIsoCokernel, Iso.trans_hom, eqToIso_refl, Iso.refl_hom, Category.id_comp,
    HomologicalComplex.isoHomologyι_hom, HomologicalComplex.homology_π_ι_assoc]
  have hπ {X Y Z W : ModuleCat.{u} R} {f : X ⟶ Y} (π : Y ⟶ Z) (w : f ≫ π = 0)
      (hc : IsColimit (CokernelCofork.ofπ π w)) (g : cokernel f ⟶ W) :
      π ≫ (hc.coconePointUniqueUpToIso (cokernelIsCokernel f)).hom ≫ g = cokernel.π f ≫ g := by
    simpa using hc.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel f) .one =≫ g
  have hconj {X X' Y Y' W : ModuleCat.{u} R} (a : X' ≅ X) (f : X ⟶ Y) (b : Y' ≅ Y)
      (w : (a.hom ≫ f ≫ b.inv) ≫ b.hom = a.hom ≫ f) (e : cokernel f ≅ W) :
      cokernel.π (a.hom ≫ f ≫ b.inv) ≫ (cokernel.mapIso _ f a b w ≪≫ e).hom =
        b.hom ≫ cokernel.π f ≫ e.hom := by
    simp
  rw [hπ, π_comp_cokernelIsoOfEq_hom_assoc]
  -- The first differential is only stated up to unfolding its intermediate objects, so the
  -- composite is computed by unification rather than by rewriting.
  refine (_ ≫= hconj _ _ _ _ _).trans ?_
  refine (_ ≫= _ ≫= π_comp_cokernelTripleδIsoOfEq_hom R hp _ _ _ _ _ q).trans ?_
  exact _ ≫= (reassoc_of% (filteredSpaceSpectralSequenceFirstPageXIso_hom_comp_eqToHom R
    (a := 0 - 1) (b := 0) (b' := 0 - 1 + 1) _ _ _ _ _ _ _
    (ofInclusion_preimageSkeleton_eq_preimageSkeletonPair 0 (0 - 1) (by lia))
    (ofInclusion_preimageSkeleton_eq_preimageSkeletonPair 0 (0 - 1) (by lia)))) _

variable (C) in
/-- Under `TauCeti.TopCat.serreSpectralSequenceSecondPageXZeroIsoCokernel`, the projection of the
first page onto the second is the quotient map of `E¹_{0,q} = Hq(p⁻¹(X⁰), p⁻¹(X⁻¹); R)` by the
transport differences along the `1`-cells. -/
@[reassoc]
lemma homologyπ_comp_serreSpectralSequenceSecondPageXZeroIsoCokernel_hom (q : ℕ) (pq : ℤ × ℤ)
    (hb : pq.2 = -1) (ha : pq.1 + pq.2 = -q) :
    ((serreSpectralSequence C p R).page 2).homologyπ pq ≫
        ((serreSpectralSequence C p R).iso 2 3 pq rfl le_rfl).hom ≫
        (serreSpectralSequenceSecondPageXZeroIsoCokernel C R hp q pq hb ha).hom =
      ((serreSpectralSequence C p R).page 2).iCycles pq ≫
        (filteredSpaceSpectralSequenceFirstPageXIso (ModuleCat.of R R)
          (monotone_preimageSkeleton p) pq pq.2 (pq.2 + 1) rfl rfl _ rfl q ha).hom ≫
        eqToHom (congrArg (fun P : TopPair.{u} ↦ P.singularHomology (ModuleCat.of R R) q)
          (ofInclusion_preimageSkeleton_eq_preimageSkeletonPair 0 pq.2 (by lia))) ≫
        cokernel.π (oneCellTransportDifference C R hp q) := by
  rw [serreSpectralSequenceSecondPageXZeroIsoCokernel, Iso.trans_hom, Iso.symm_hom,
    Iso.hom_inv_id_assoc, homologyπ_comp_homologyIsoCokernel_hom]

end SecondPage

end TopCat
end TauCeti
