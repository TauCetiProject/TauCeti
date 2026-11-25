/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AlternatingConst
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Basic
public import TauCeti.AlgebraicTopology.Singular.Basic
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.RingTheory.Flat.CategoryTheory
import TauCeti.Algebra.Homology.CyclesComplex
import TauCeti.Algebra.Homology.ModuleCat.FlatCycles
import TauCeti.AlgebraicTopology.Singular.Empty

/-!
# The singular chains of a point

The singular chain complex of a one-point space `X`, with coefficients in an object `R` of a
preadditive category, is isomorphic to the alternating constant complex
`ChainComplex.alternatingConst.obj R` (`TauCeti.pointSingularChainIsoAlternatingConst`), and hence
chain homotopy equivalent to `R` placed in degree zero (`TauCeti.pointSingularChainHomotopyEquiv`).
The forward map is the augmentation, which sends the unique singular vertex to the identity of `R`,
and the inverse includes `R` as the summand of that vertex. In every positive even degree `n`, the
outgoing differential is an isomorphism, so the cycles vanish and `Cₙ(X; R) / Zₙ(X; R) ≅ R`
(`TauCeti.pointCokernelICyclesIso`).

Unlike the vanishing of positive-degree homology, a chain homotopy equivalence survives any
additive functor. Applying `Hom(-, M)` to it computes the singular cohomology of a point with
arbitrary coefficients (`TauCeti.pointSingularCochainHomotopyEquiv`), without projectivity or
injectivity assumptions.

For a nonempty space `Y` and a module `N` over a commutative ring `k`, retracting onto a point
recovers flatness of `N` from flatness of `Cₙ(Y; N) / Zₙ(Y; N)` in any positive even degree
(`TopCat.flat_of_flat_cokernel_iCycles_of_even`) or from flatness of `H₀(Y; N)`
(`TopCat.flat_of_flat_singularHomology_zero`). Together with the vanishing of singular chains on an
empty space, `TopCat.flat_singularChainComplex_X` deduces degreewise flatness of `C(Y; N)` from
flatness of `N` when `Y` is nonempty.

A point is totally disconnected, so Mathlib identifies its singular chains with the alternating
constant complex on the coefficients summed over the point
(`AlgebraicTopology.singularChainComplexFunctorIsoOfTotallyDisconnectedSpace`), and that complex
contracts onto its degree-zero term (`ChainComplex.alternatingConstHomotopyEquiv`, from the extra
degeneracy `SimplicialObject.Augmented.ExtraDegeneracy.const`). The construction of the
contraction, and of its cochain counterpart, follows the unmerged Tau Ceti pull request
https://github.com/TauCetiProject/TauCeti/pull/20882.

## Main declarations

* `TauCeti.pointSingularChainIsoAlternatingConst`: the isomorphism between the singular chains of a
  one-point space and `ChainComplex.alternatingConst.obj R`.
* `TauCeti.pointCokernelICyclesIso`: `R ≅ Cₙ(X; R) / Zₙ(X; R)` for a one-point space `X` and
  positive even `n`.
* `TauCeti.pointSingularChainHomotopyEquiv`: the chain homotopy equivalence between the singular
  chains of a one-point space and the coefficients in degree zero.
* `TauCeti.ιChainComplex_pointSingularChainHomotopyEquiv_hom_f_zero` and
  `TauCeti.pointSingularChainHomotopyEquiv_inv_f_zero`: the forward map is the augmentation and
  the inverse is the inclusion of the unique vertex.
* `TauCeti.isIso_pointSingularChainHomotopyEquiv_hom_f_zero`: in degree zero the augmentation is
  an isomorphism.
* `TauCeti.pointSingularChainHomotopyEquiv_hom_naturality`: the augmentation is natural in the
  coefficients.
* `TopCat.flat_of_flat_cokernel_iCycles_of_even`: flatness of `Cₙ(Y; N) / Zₙ(Y; N)` in positive
  even degree for a nonempty space `Y` implies flatness of `N`.
* `TopCat.flat_of_flat_singularHomology_zero`: flatness of `H₀(X; M)` for a nonempty space `X`
  implies flatness of `M`.
* `TopCat.flat_singularChainComplex_X`: degreewise flatness of `C(X; M)` from flatness of `M` when
  `X` is nonempty.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.1, the homology of a point.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology
open scoped Simplicial

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C] [HasZeroObject C]
  (R : C) (X : TopCat.{w}) [Unique X]

/-- **The singular chains of a point contract onto the coefficients.** For a one-point space `X`,
the singular chain complex with coefficients in `R` is chain homotopy equivalent to `R` in
degree zero. The forward map is the augmentation and the inverse is the inclusion of the unique
vertex. -/
def pointSingularChainHomotopyEquiv :
    HomotopyEquiv ((TopCat.toSSet.obj X).chainComplex R) ((ChainComplex.single₀ C).obj R) :=
  (HomotopyEquiv.ofIso (singularChainComplexFunctorIsoOfTotallyDisconnectedSpace C R X)).trans
    ((ChainComplex.alternatingConstHomotopyEquiv _).trans
      (HomotopyEquiv.ofIso ((ChainComplex.single₀ C).mapIso (coproductUniqueIso fun _ : X ↦ R))))

/-- The augmentation sends the summand of the unique singular vertex of a point identically to
the coefficients. -/
@[simp, reassoc]
lemma ιChainComplex_pointSingularChainHomotopyEquiv_hom_f_zero
    (σ : (TopCat.toSSet.obj X) _⦋0⦌) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ (pointSingularChainHomotopyEquiv R X).hom.f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 R).inv := by
  rw [pointSingularChainHomotopyEquiv, HomotopyEquiv.trans_hom, HomotopyEquiv.trans_hom,
    HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    ChainComplex.alternatingConstHomotopyEquiv_hom_f_zero]
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _)
    (ιChainComplex_singularChainComplexFunctorIsoOfTotallyDisconnectedSpace_hom_f_zero
      R X σ)).trans ?_
  simp only [HomotopyEquiv.ofIso, Functor.mapIso_hom, ChainComplex.single₀_map_f_zero,
    ChainComplex.single₀ObjXSelf, Iso.refl_inv]
  exact (congrArg _ (Category.id_comp _)).trans
    ((ι_coproductUniqueIso_hom _ _).trans (eqToHom_refl _ _))

/-- In degree zero, the augmentation of the singular chains of a point is an isomorphism. -/
instance isIso_pointSingularChainHomotopyEquiv_hom_f_zero :
    IsIso ((pointSingularChainHomotopyEquiv R X).hom.f 0) := by
  rw [pointSingularChainHomotopyEquiv, HomotopyEquiv.trans_hom, HomotopyEquiv.trans_hom,
    HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    ChainComplex.alternatingConstHomotopyEquiv_hom_f_zero]
  exact IsIso.comp_isIso' (inferInstanceAs
    (IsIso ((singularChainComplexFunctorIsoOfTotallyDisconnectedSpace C R X).hom.f 0)))
    (IsIso.comp_isIso' (Iso.isIso_inv _) (inferInstanceAs
      (IsIso (((ChainComplex.single₀ C).mapIso (coproductUniqueIso fun _ : X ↦ R)).hom.f 0))))

/-- The inverse of the contraction of the singular chains of a point includes the coefficients
as the summand of the unique singular vertex. -/
lemma pointSingularChainHomotopyEquiv_inv_f_zero (σ : (TopCat.toSSet.obj X) _⦋0⦌) :
    (pointSingularChainHomotopyEquiv R X).inv.f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 R).hom ≫
        (TopCat.toSSet.obj X).ιChainComplex σ := by
  -- The homotopy `inv ≫ hom ≃ 𝟙` has no room to act in degree zero of `R[0]`.
  have h := (pointSingularChainHomotopyEquiv R X).homotopyInvHomId.comm 0
  rw [Homotopy.prevD_chainComplex, Homotopy.dNext_zero_chainComplex] at h
  rw [← cancel_mono ((pointSingularChainHomotopyEquiv R X).hom.f 0), Category.assoc,
    ιChainComplex_pointSingularChainHomotopyEquiv_hom_f_zero, Iso.hom_inv_id]
  simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f, HomologicalComplex.single_obj_d,
    comp_zero, zero_add] using h

/-- The augmentation of the singular chains of a point is natural in the coefficients. -/
@[reassoc]
lemma pointSingularChainHomotopyEquiv_hom_naturality {S : C} (f : R ⟶ S) :
    ((SSet.chainComplexFunctor C).map f).app (TopCat.toSSet.obj X) ≫
        (pointSingularChainHomotopyEquiv S X).hom =
      (pointSingularChainHomotopyEquiv R X).hom ≫ (ChainComplex.single₀ C).map f := by
  apply HomologicalComplex.to_single_hom_ext
  ext σ
  simp only [HomologicalComplex.comp_f, SSet.ιChainComplex_chainComplexFunctor_map_app_f_assoc,
    ιChainComplex_pointSingularChainHomotopyEquiv_hom_f_zero,
    ιChainComplex_pointSingularChainHomotopyEquiv_hom_f_zero_assoc]
  simp

/-- For a one-point space `X`, the singular chain complex `C(X; R)` is isomorphic to the
alternating constant complex `ChainComplex.alternatingConst.obj R`. -/
def pointSingularChainIsoAlternatingConst :
    (TopCat.toSSet.obj X).chainComplex R ≅ ChainComplex.alternatingConst.obj R :=
  singularChainComplexFunctorIsoOfTotallyDisconnectedSpace C R X ≪≫
    ChainComplex.alternatingConst.mapIso (coproductUniqueIso fun _ : X ↦ R)

/-- In every positive even degree `n`, the differential out of `Cₙ(X; R)` for a one-point space `X`
is an isomorphism, so its cycles vanish and `Cₙ(X; R) / Zₙ(X; R) ≅ R`. -/
def pointCokernelICyclesIso [CategoryWithHomology C] (n : ℕ) (hn : Even n) (h0 : n ≠ 0)
    [HasCokernel (((TopCat.toSSet.obj X).chainComplex R).iCycles n)] :
    R ≅ cokernel (((TopCat.toSSet.obj X).chainComplex R).iCycles n) := by
  let e := pointSingularChainIsoAlternatingConst R X
  have hd : IsIso (((TopCat.toSSet.obj X).chainComplex R).d n (n - 1)) := by
    have hrel : n - 1 + 1 = n := by omega
    have hcomm := (e.hom.comm n (n - 1)).symm
    have heq : ((TopCat.toSSet.obj X).chainComplex R).d n (n - 1) =
        e.hom.f n ≫ (ChainComplex.alternatingConst.obj R).d n (n - 1) ≫ e.inv.f (n - 1) := by
      rw [← Category.assoc, ← hcomm, Category.assoc, ← HomologicalComplex.comp_f, Iso.hom_inv_id,
        HomologicalComplex.id_f, Category.comp_id]
    have hd' : (ChainComplex.alternatingConst.obj R).d n (n - 1) = 𝟙 R := by
      simp [ChainComplex.alternatingConst, hrel, hn]
    rw [heq, hd']
    have : IsIso (e.hom.f n) := ((HomologicalComplex.eval C _ n).mapIso e).isIso_hom
    have : IsIso (e.inv.f (n - 1)) := ((HomologicalComplex.eval C _ (n - 1)).mapIso e).isIso_inv
    have : IsIso (𝟙 R ≫ e.inv.f (n - 1)) := IsIso.comp_isIso
    exact IsIso.comp_isIso
  have hZ0 : IsZero (((TopCat.toSSet.obj X).chainComplex R).cycles n) := by
    rw [IsZero.iff_id_eq_zero,
      ← cancel_mono (((TopCat.toSSet.obj X).chainComplex R).iCycles n),
      ← cancel_mono (((TopCat.toSSet.obj X).chainComplex R).d n (n - 1))]
    simp [((TopCat.toSSet.obj X).chainComplex R).iCycles_d n (n - 1)]
  have hi0 : ((TopCat.toSSet.obj X).chainComplex R).iCycles n = 0 := hZ0.eq_of_src _ _
  exact ((HomologicalComplex.eval C _ n).mapIso e).symm ≪≫
    { hom := cokernel.π _
      inv := cokernel.desc _ (𝟙 _) (by rw [hi0, zero_comp])
      hom_inv_id := by simp
      inv_hom_id := coequalizer.hom_ext (by simp) }

end TauCeti

namespace TopCat

/-- If `Y` is nonempty and `Cₙ(Y; N) / Zₙ(Y; N)` is flat in some positive even degree `n`, then
`N` is a retract of `Cₙ(Y; N) / Zₙ(Y; N)` via a point of `Y`, hence flat. -/
theorem flat_of_flat_cokernel_iCycles_of_even {k : Type u} [CommRing k]
    (Y : TopCat.{w}) [Nonempty Y] (N : ModuleCat.{max w v} k) (n : ℕ) (hn : Even n) (h0 : n ≠ 0)
    [Module.Flat k (cokernel (((toSSet.obj Y).chainComplex N).iCycles n) : ModuleCat.{max w v} k)] :
    Module.Flat k N := by
  let pt : TopCat.{w} := TopCat.of PUnit
  let iPt : pt ⟶ Y := TopCat.ofHom (ContinuousMap.const _ (Classical.arbitrary Y))
  let rPt : Y ⟶ pt := TopCat.ofHom (ContinuousMap.const _ PUnit.unit)
  have hir : iPt ≫ rPt = 𝟙 pt := ConcreteCategory.hom_ext _ _ fun _ ↦ rfl
  let φ := SSet.chainComplexMap (toSSet.map iPt) N
  let ψ := SSet.chainComplexMap (toSSet.map rPt) N
  have hφψ : φ ≫ ψ = 𝟙 ((toSSet.obj pt).chainComplex N) :=
    HomologicalComplex.hom_ext _ _ fun m ↦ by
      rw [HomologicalComplex.comp_f, SSet.chainComplexMap_f_comp, ← CategoryTheory.Functor.map_comp,
        hir, CategoryTheory.Functor.map_id, SSet.chainComplexMap_id]
  let ι := (HomologicalComplex.cyclesComplexShortComplexMap φ).τ₃.f n
  let ρ := (HomologicalComplex.cyclesComplexShortComplexMap ψ).τ₃.f n
  have hιρ : ι ≫ ρ = 𝟙 _ :=
    congrArg (fun m ↦ m.τ₃.f n)
      ((HomologicalComplex.cyclesComplexShortComplexMap_comp φ ψ).symm.trans
        (by rw [hφψ, HomologicalComplex.cyclesComplexShortComplexMap_id]))
  have hflat : Module.Flat k (((toSSet.obj pt).chainComplex N).cyclesComplexShortComplex.X₃.X n) :=
    Module.Flat.of_retract ι.hom ρ.hom (congrArg ModuleCat.Hom.hom hιρ)
  rw [HomologicalComplex.cyclesComplexShortComplex_X₃, HomologicalComplex.graded_X] at hflat
  exact Module.Flat.of_linearEquiv (TauCeti.pointCokernelICyclesIso N pt n hn h0).toLinearEquiv

/-- If `X` is nonempty and `H₀(X; M)` is flat, then `M` is a retract of `H₀(X; M)` via a connected
component of `X`, hence flat. -/
theorem flat_of_flat_singularHomology_zero {k : Type u} [CommRing k]
    (X : TopCat.{w}) [Nonempty X] (M : ModuleCat.{max w v} k)
    [Module.Flat k (((singularHomologyFunctor (ModuleCat.{max w v} k) 0).obj M).obj X)] :
    Module.Flat k M := by
  have : Module.Flat k (∐ fun _ : ZerothHomotopy X ↦ M : ModuleCat.{max w v} k) :=
    Module.Flat.of_linearEquiv (X.singularHomology₀Iso M).symm.toLinearEquiv
  let i : M ⟶ ∐ fun _ : ZerothHomotopy X ↦ M :=
    Sigma.ι (fun _ : ZerothHomotopy X ↦ M) (Quot.mk _ (Classical.arbitrary X))
  let r : (∐ fun _ : ZerothHomotopy X ↦ M) ⟶ M := Sigma.desc fun _ ↦ 𝟙 M
  exact Module.Flat.of_retract i.hom r.hom (congrArg ModuleCat.Hom.hom (by simp [i, r]))

/-- The singular chain module `C_q(X; M)` is flat whenever `M` is flat on nonempty `X` (for empty
`X` the chain module is zero, hence flat). -/
theorem flat_singularChainComplex_X {k : Type u} [CommRing k]
    (X : TopCat.{w}) (M : ModuleCat.{max w v} k) (h : Nonempty X → Module.Flat k M) (q : ℕ) :
    Module.Flat k (((toSSet.obj X).chainComplex M).X q) := by
  by_cases hX : Nonempty X
  · have := h hX
    exact SSet.flat_chainComplex_X (toSSet.obj X) M q
  · have : IsEmpty X := not_nonempty_iff.1 hX
    have : Subsingleton (((toSSet.obj X).chainComplex M).X q) :=
      ModuleCat.subsingleton_of_isZero
        ((HomologicalComplex.eval _ _ q).map_isZero ((toSSet.obj X).isZero_chainComplex M))
    exact Module.Flat.of_free

end TopCat
