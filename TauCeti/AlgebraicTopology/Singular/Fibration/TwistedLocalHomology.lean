/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient.Contractible
public import TauCeti.AlgebraicTopology.Singular.Fibration.LocalHomology
public import TauCeti.AlgebraicTopology.Singular.Twisted.ConstantNaturality
public import TauCeti.AlgebraicTopology.Singular.Twisted.Excision

/-!
# Local homology of a Serre fibration along a fibre, with coefficients from the base

Let `p : E → B` be a Serre fibration over a `T₁` space `B`, and let `b` lie in the source of an
open partial homeomorphism `e : B → V` to a real normed space of finite dimension `r`, such as a
chart of a topological manifold modelled on `V`. For a local coefficient system `L` on `B`, this
file computes the local homology of `E` along the fibre `F = p⁻¹(b)` with coefficients in the
pulled-back system `p*L`:

* `Hₘ(E, E ∖ F; p*L) = 0` for `m < r` (`TauCeti.TopCat.isZero_twistedHomology_complFiber`);
* `Hₙ₊ᵣ(E, E ∖ F; p*L) ≅ Hₙ(F; L_b)`, with coefficients in the fibre `L_b` of `L` over `b`
  (`TauCeti.TopCat.twistedHomologyComplFiberIso`).

This is the untwisted computation of `TauCeti.AlgebraicTopology.Singular.Fibration.LocalHomology`
(`TauCeti.TopCat.singularHomologyComplFiberIso`) with the coefficients allowed to vary over the
base. Barraud, Damian, Humilière and Oancea need it for bases that are not orientable, where the
fundamental class lives in homology with coefficients in the orientation system `or_B` and the
classes of the total space that can live over it carry the coefficients `p*or_B`. The composite
`Hₙ₊ᵣ(E; p*L) → Hₙ₊ᵣ(E, E ∖ F; p*L) ≅ Hₙ(F; L_b)` is then the shriek map of the inclusion of the
point `b`, and a class is detected by it exactly when its localization along `F` is nonzero
(`TauCeti.TopCat.twistedHomologyπ_comp_twistedHomologyComplFiberIso_hom_ne_zero_iff`). For
`L = or_B`, a local orientation at `b` identifies `L_b` with the ground ring.

## The computation

Choose a ball of positive radius `ε` about `e b` inside the target of `e`, and let `U` be its
preimage in the source of `e` (`OpenPartialHomeomorph.chartBall`). The chart ball contracts onto
`b` (`OpenPartialHomeomorph.chartBallContraction`), so the restriction of `L` to it is the constant
system at `L_b` (`TauCeti.LocalCoefficientSystem.isoConstantOfHomotopy`), and so is the
restriction of `p*L` to the open set `p⁻¹(U)`, which contains the closed fibre `F`
(`TauCeti.TopCat.chartBallCoefficientIso`). Relative homology modulo the complement of `F` only
sees the coefficients near `F` (`TopPair.twistedHomologyComplIsoOfRestrictIso`), so
`Hₘ(E, E ∖ F; p*L) ≅ Hₘ(E, E ∖ F; L_b)`, and the untwisted computation finishes the proof. After
excision onto `p⁻¹(U)` the isomorphism is this change of coefficients followed by the untwisted
one (`TauCeti.TopCat.twistedHomologyMap_excisionMap_comp_twistedHomologyComplFiberIso_hom`), and
for a constant system on `B` it is the untwisted one
(`TauCeti.TopCat.twistedHomologyComplFiberIso_hom_constant`).

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §2.4, Definition 2.3, Proposition 2.6
  and Lemma 2.9.
* A. Hatcher, *Algebraic Topology*, Section 3.H.
-/

public section

noncomputable section

open CategoryTheory Module Metric Set Topology TauCeti.LocalCoefficientSystem

universe u

namespace TauCeti

namespace TopCat

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] {E B : _root_.TopCat.{u}}
  {p : E ⟶ B} {R : Type*} [Ring R] (L : LocalCoefficientSystem.{_, u, u} R B)
  (e : OpenPartialHomeomorph B V) {b : B} (hb : b ∈ e.source) {ε : ℝ}
  (hε : ball (e b) ε ⊆ e.target) (hε₀ : 0 < ε)

/-- The restriction of `p*L` to the part of `E` over the chart ball `e.chartBall b ε` is the
constant system at the fibre `L_b`: it is pulled back, along the restriction of `p`, from the
restriction of `L` to the chart ball, which its contraction onto `b` identifies with the constant
system (`TauCeti.LocalCoefficientSystem.isoConstantOfHomotopy`). At a point `z` the comparison is
transport by `L` along the path traced by `p z` under the contraction
(`TauCeti.TopCat.chartBallCoefficientIso_hom_app`). -/
def chartBallCoefficientIso :
    (pullback (R := R) (⟨Subtype.val, continuous_subtype_val⟩ :
        C(_root_.TopCat.of (p ⁻¹' e.chartBall b ε), E))).obj ((pullback p.hom).obj L) ≅
      (constantFunctor _).obj (L.obj (FundamentalGroupoid.mk b)) :=
  -- The two factorizations `p ∘ val` and `val ∘ p.restrictPreimage` of the restriction of `p` are
  -- the same continuous map by definition, so the two `pullbackCompIso` compose directly.
  ((pullbackCompIso _ p.hom).app L).symm ≪≫
    (pullbackCompIso (X := _root_.TopCat.of (p ⁻¹' e.chartBall b ε))
      (Y := _root_.TopCat.of (e.chartBall b ε)) (p.hom.restrictPreimage (e.chartBall b ε))
      ⟨Subtype.val, continuous_subtype_val⟩).app L ≪≫
    (pullback _).mapIso (isoConstantOfHomotopy (X := _root_.TopCat.of (e.chartBall b ε))
      (e.chartBallContraction hb hε hε₀) _) ≪≫
    pullbackConstantIso _ _

/-- At a point `z` over the chart ball, `TauCeti.TopCat.chartBallCoefficientIso` is transport by
`L` along the path traced by `p z` under the contraction of the chart ball onto `b`. -/
@[simp]
lemma chartBallCoefficientIso_hom_app
    (z : FundamentalGroupoid (_root_.TopCat.of (p ⁻¹' e.chartBall b ε))) :
    (chartBallCoefficientIso L e hb hε hε₀).hom.app z =
      ((pullback (R := R) (⟨Subtype.val, continuous_subtype_val⟩ :
        C(_root_.TopCat.of (e.chartBall b ε), B))).obj L).map
        ⟦(e.chartBallContraction hb hε hε₀).evalAt
          (p.hom.restrictPreimage (e.chartBall b ε) z.as)⟧ := by
  simp only [chartBallCoefficientIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
    NatTrans.comp_app, pullbackCompIso_inv_app_app]
  -- With `q` the restriction of `p`, the pieces of the composite meet at objects that agree only
  -- by definition: first `(pullback (p ∘ val)).obj L` and `(pullback (val ∘ q)).obj L`, then
  -- `(pullback val ⋙ pullback q).obj L` and `(pullback q).obj ((pullback val).obj L)`. So
  -- `Iso.trans_hom` cannot be rewritten there, and is applied at each of them by `congrArg`.
  refine (Category.id_comp _).trans ((congrArg (NatTrans.app · z) (Iso.trans_hom _ _)).trans ?_)
  rw [NatTrans.comp_app, Iso.app_hom, pullbackCompIso_hom_app_app]
  refine (Category.id_comp _).trans ((congrArg (NatTrans.app · z) (Iso.trans_hom _ _)).trans ?_)
  simp only [NatTrans.comp_app, Functor.mapIso_hom, pullback_map_app,
    isoConstantOfHomotopy_hom_app, pullbackConstantIso_hom_app]
  -- The two path classes agree by definition: both trace `p z` under the contraction.
  exact Category.comp_id _

variable [T1Space B]

/-- The identification `Hₘ(E, E ∖ p⁻¹(b); p*L) ≅ Hₘ(E, E ∖ p⁻¹(b); L_b)` given by
`TauCeti.TopCat.chartBallCoefficientIso` near the fibre. Its type is left to be inferred: stating
the target `TopPair.singularHomology` here would search again for the coproducts of modules that
`TopPair.twistedHomologyConstantIso` already carries, and that search times out. -/
private def twistedHomologyComplFiberCoefficientIso (m : ℕ) :=
  TopPair.twistedHomologyComplIsoOfRestrictIso
      ((e.isOpen_chartBall b ε).preimage p.hom.continuous)
      ((isClosed_singleton.preimage p.hom.continuous).closure_subset.trans
        (preimage_mono (singleton_subset_iff.2 (e.mem_chartBall_self hb hε₀))))
      (chartBallCoefficientIso L e hb hε hε₀ ≪≫ (pullbackConstantIso _ _).symm) m ≪≫
    (TopPair.ofSubset (p ⁻¹' {b})ᶜ).twistedHomologyConstantIso (L.obj (FundamentalGroupoid.mk b)) m

/-- **The homology of a Serre fibration modulo the complement of a fibre, with coefficients from
the base, is the shifted homology of the fibre.** Let `p : E ⟶ B` be a Serre fibration over a `T₁`
space, `L` a local coefficient system on `B`, and `b` a point in the source of an open partial
homeomorphism `e : B → V` to a real normed space of finite dimension `r`. Then
`Hₘ(E, E ∖ p⁻¹(b); p*L) ≅ Hₙ(p⁻¹(b); L_b)` for `m = n + r`.

The isomorphism depends on `e` and on a ball of radius `ε` about `e b` inside the target of `e`:
the restriction of `L` to the corresponding chart ball is identified with the constant system at
`L_b` along its contraction onto `b`, and the resulting identification
`Hₘ(E, E ∖ p⁻¹(b); p*L) ≅ Hₘ(E, E ∖ p⁻¹(b); L_b)` is followed by
`TauCeti.TopCat.singularHomologyComplFiberIso`
(`TauCeti.TopCat.twistedHomologyMap_excisionMap_comp_twistedHomologyComplFiberIso_hom`). -/
def twistedHomologyComplFiberIso (hp : serreFibrations p) (n m : ℕ) (h : n + finrank ℝ V = m)
    [FiniteDimensional ℝ V] :
    (TopPair.ofSubset (p ⁻¹' {b})ᶜ).twistedHomology ((pullback p.hom).obj L) m ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
        (L.obj (FundamentalGroupoid.mk b))).obj (_root_.TopCat.of (p ⁻¹' {b})) :=
  twistedHomologyComplFiberCoefficientIso L e hb hε hε₀ m ≪≫
    singularHomologyComplFiberIso _ e hb hε hε₀ hp n m h

/-- The isomorphism `TauCeti.TopCat.twistedHomologyComplFiberIso` commutes with excision onto the
part of `E` over `OpenPartialHomeomorph.chartBall e b ε`: after excision it is the change of
coefficients along `TauCeti.TopCat.chartBallCoefficientIso`, the comparison of twisted homology
with constant coefficients and ordinary homology, and the untwisted
`TauCeti.TopCat.singularHomologyComplFiberIso` after excision. -/
@[reassoc]
lemma twistedHomologyMap_excisionMap_comp_twistedHomologyComplFiberIso_hom
    [FiniteDimensional ℝ V] (hp : serreFibrations p) (n m : ℕ) (h : n + finrank ℝ V = m) :
    TopPair.twistedHomologyMap
        (TopPair.excisionMap (X := E) (p ⁻¹' e.chartBall b ε) (p ⁻¹' {b})ᶜ)
        ((pullback p.hom).obj L) m ≫
        (twistedHomologyComplFiberIso L e hb hε hε₀ hp n m h).hom =
      (TopPair.interPair (p ⁻¹' e.chartBall b ε) (p ⁻¹' {b})ᶜ).twistedHomologyCoefficientMap
          (eqToHom (TopPair.pullback_obj_fst_excisionMap (R := R) _ _ ((pullback p.hom).obj L)) ≫
            (chartBallCoefficientIso L e hb hε hε₀).hom) m ≫
        ((TopPair.interPair (p ⁻¹' e.chartBall b ε) (p ⁻¹' {b})ᶜ).twistedHomologyConstantIso
          (L.obj (FundamentalGroupoid.mk b)) m).hom ≫
        TopPair.singularHomologyMap
          (TopPair.excisionMap (X := E) (p ⁻¹' e.chartBall b ε) (p ⁻¹' {b})ᶜ)
          (L.obj (FundamentalGroupoid.mk b)) m ≫
        (singularHomologyComplFiberIso _ e hb hε hε₀ hp n m h).hom := by
  rw [twistedHomologyComplFiberIso, Iso.trans_hom, twistedHomologyComplFiberCoefficientIso]
  -- The ambient space of `(E, E ∖ p⁻¹(b))` is `E` only up to unfolding `TopPair.ofSubset`, so the
  -- composite of `twistedHomologyComplFiberCoefficientIso` and the naturality of the constant
  -- comparison along the excision inclusion are applied with `erw`.
  erw [Iso.trans_hom]
  rw [← Category.assoc, ← Category.assoc,
    TopPair.twistedHomologyMap_excisionMap_comp_twistedHomologyComplIsoOfRestrictIso_hom]
  simp only [Category.assoc]
  erw [TopPair.twistedHomologyConstantIso_hom_pair_naturality_assoc]
  erw [← TopPair.twistedHomologyCoefficientMap_comp_assoc]
  congr 2
  -- The coefficient identification is transported along the equation of the ambient map of the
  -- excision inclusion with the inclusion of `p⁻¹(U)`. The ambient spaces of the excision inclusion
  -- are `p⁻¹(U)` and `E` only up to unfolding `TopPair.interPair` and `TopPair.ofSubset`, so the
  -- goal cannot be rewritten; generalize that equation to discharge it.
  have key : ∀ {f g : C(_root_.TopCat.of (p ⁻¹' e.chartBall b ε), E)} (hfg : f = g)
      (φ : (pullback (R := R) g).obj ((pullback p.hom).obj L) ⟶
        (constantFunctor _).obj (L.obj (FundamentalGroupoid.mk b))),
      (eqToHom (congrArg (fun f ↦ (pullback (R := R) f).obj ((pullback p.hom).obj L)) hfg) ≫
          φ ≫ (pullbackConstantIso g _).inv ≫
            eqToHom (congrArg (fun f ↦ (pullback (R := R) f).obj
              ((constantFunctor E).obj (L.obj (FundamentalGroupoid.mk b)))) hfg).symm) ≫
        (pullbackConstantIso f _).hom =
      eqToHom (congrArg (fun f ↦ (pullback (R := R) f).obj ((pullback p.hom).obj L)) hfg) ≫ φ := by
    rintro f g rfl φ
    simp
  exact key (ContinuousMap.ext (TopPair.excisionMap_fst_apply _ _) :
    (TopPair.Hom.fst (TopPair.excisionMap (X := E) (p ⁻¹' e.chartBall b ε) (p ⁻¹' {b})ᶜ)).hom =
      ⟨Subtype.val, continuous_subtype_val⟩) _

include e hb in
/-- **The homology of a Serre fibration modulo the complement of a fibre, with coefficients from
the base, vanishes below the dimension.** Let `p : E ⟶ B` be a Serre fibration over a `T₁` space,
`L` a local coefficient system on `B`, and `b` a point in the source of an open partial
homeomorphism `e : B → V` to a finite-dimensional real normed space. Then
`Hₘ(E, E ∖ p⁻¹(b); p*L) = 0` for every `m < dim V`. -/
theorem isZero_twistedHomology_complFiber [FiniteDimensional ℝ V] (hp : serreFibrations p)
    {m : ℕ} (hm : m < finrank ℝ V) :
    Limits.IsZero
      ((TopPair.ofSubset (p ⁻¹' {b})ᶜ).twistedHomology ((pullback p.hom).obj L) m) := by
  obtain ⟨ε, hε₀, hε⟩ := Metric.isOpen_iff.1 e.open_target (e b) (e.map_source hb)
  exact (isZero_singularHomology_complFiber _ e hb hp hm).of_iso
    (twistedHomologyComplFiberCoefficientIso L e hb hε hε₀ m)

/-- A class `α ∈ Hₘ(E; p*L)` is detected by the shriek map
`Hₘ(E; p*L) → Hₘ(E, E ∖ p⁻¹(b); p*L) ≅ Hₙ(p⁻¹(b); L_b)` of the inclusion of `b`, for
`m = n + dim V`, exactly when its localization along the fibre is nonzero. In particular whether
it is detected does not depend on the chart. -/
theorem twistedHomologyπ_comp_twistedHomologyComplFiberIso_hom_ne_zero_iff
    [FiniteDimensional ℝ V] (hp : serreFibrations p) (n m : ℕ) (h : n + finrank ℝ V = m)
    (α : ((pullback p.hom).obj L).twistedHomology m) :
    ((TopPair.ofSubset (p ⁻¹' {b})ᶜ).twistedHomologyπ _ m ≫
        (twistedHomologyComplFiberIso L e hb hε hε₀ hp n m h).hom).hom α ≠ 0 ↔
      ((TopPair.ofSubset (p ⁻¹' {b})ᶜ).twistedHomologyπ _ m).hom α ≠ 0 :=
  not_congr (twistedHomologyComplFiberIso L e hb hε hε₀ hp n m h).toLinearEquiv.map_eq_zero_iff

/-- For a constant system `M` on `B`, the isomorphism
`TauCeti.TopCat.twistedHomologyComplFiberIso` is the comparison of twisted homology with constant
coefficients and ordinary homology, followed by the untwisted
`TauCeti.TopCat.singularHomologyComplFiberIso`. -/
lemma twistedHomologyComplFiberIso_hom_constant [FiniteDimensional ℝ V] (M : ModuleCat.{u} R)
    (hp : serreFibrations p) (n m : ℕ) (h : n + finrank ℝ V = m) :
    (twistedHomologyComplFiberIso ((constantFunctor B).obj M) e hb hε hε₀ hp n m h).hom =
      (TopPair.ofSubset (p ⁻¹' {b})ᶜ).twistedHomologyCoefficientMap
          (pullbackConstantIso p.hom M).hom m ≫
        ((TopPair.ofSubset (p ⁻¹' {b})ᶜ).twistedHomologyConstantIso M m).hom ≫
          (singularHomologyComplFiberIso M e hb hε hε₀ hp n m h).hom := by
  have hcoef : chartBallCoefficientIso ((constantFunctor B).obj M) e hb hε hε₀ ≪≫
      (pullbackConstantIso _ M).symm = (pullback _).mapIso (pullbackConstantIso p.hom M) := by
    refine Iso.ext (NatTrans.ext (funext fun x ↦ ?_))
    -- The composite is only definitionally glued at `(pullback _).obj ((constantFunctor _).obj
    -- M)`, so `Iso.trans_hom` and the transport in the constant system `M` need `erw`.
    erw [Iso.trans_hom, NatTrans.comp_app, chartBallCoefficientIso_hom_app, pullback_obj_map,
      constantFunctor_obj_map]
    simp
  rw [twistedHomologyComplFiberIso, Iso.trans_hom, twistedHomologyComplFiberCoefficientIso]
  -- As in `twistedHomologyMap_excisionMap_comp_twistedHomologyComplFiberIso_hom`, the ambient
  -- space of `(E, E ∖ p⁻¹(b))` is `E` only up to unfolding `TopPair.ofSubset`.
  erw [Iso.trans_hom, hcoef, TopPair.twistedHomologyComplIsoOfRestrictIso_hom_of_iso]
  exact Category.assoc _ _ _

end TopCat

end TauCeti
