/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient.Contractible
public import TauCeti.AlgebraicTopology.Singular.Fibration.LocalHomology
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
restriction of `p*L` to the open set `p⁻¹(U)`, which contains the closed fibre `F`. Relative
homology modulo the complement of `F` only sees the coefficients near `F`
(`TopPair.twistedHomologyComplIso`), so `Hₘ(E, E ∖ F; p*L) ≅ Hₘ(E, E ∖ F; L_b)`, and the
untwisted computation finishes the proof. For a constant system on `B`, the isomorphism is the
untwisted one (`TauCeti.TopCat.twistedHomologyComplFiberIso_hom_constant`).

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
  (e : OpenPartialHomeomorph B V) {b : B} (hb : b ∈ e.source) {ε : ℝ} (hε₀ : 0 < ε)
  (hε : ball (e b) ε ⊆ e.target)

/-- The restriction of `p` to the part of `E` over the chart ball `e.chartBall b ε`. -/
private abbrev chartBallRestrict (p : E ⟶ B) (e : OpenPartialHomeomorph B V) (b : B) (ε : ℝ) :
    C(_root_.TopCat.of (p ⁻¹' e.chartBall b ε), _root_.TopCat.of (e.chartBall b ε)) :=
  p.hom.restrictPreimage (e.chartBall b ε)

/-- The restriction of `p*L` to the part of `E` over the chart ball `e.chartBall b ε` is the
constant system at the fibre `L_b`: it is pulled back from the restriction of `L` to the chart
ball, which its contraction onto `b` identifies with the constant system. At a point `z` the
comparison is transport by `L` along the path traced by `p z` under the contraction. -/
private def chartBallCoefficientIso :
    (pullback (R := R) (⟨Subtype.val, continuous_subtype_val⟩ :
        C(_root_.TopCat.of (p ⁻¹' e.chartBall b ε), E))).obj ((pullback p.hom).obj L) ≅
      (constantFunctor _).obj (L.obj (FundamentalGroupoid.mk b)) :=
  NatIso.ofComponents
    (fun z ↦ (isoConstantOfHomotopy (X := _root_.TopCat.of (e.chartBall b ε))
      (e.chartBallContraction hb hε₀ hε)
      ((pullback (R := R) (⟨Subtype.val, continuous_subtype_val⟩ :
        C(_root_.TopCat.of (e.chartBall b ε), B))).obj L)).app
      ((FundamentalGroupoid.map (chartBallRestrict p e b ε)).obj z))
    (fun γ ↦ by
      -- `p ∘ val` and `val ∘ chartBallRestrict` are the same map `z ↦ p z.1`, so they send `γ`
      -- to the same path class of `B`.
      have hγ : (FundamentalGroupoid.map p.hom).map
            ((FundamentalGroupoid.map (⟨Subtype.val, continuous_subtype_val⟩ :
              C(_root_.TopCat.of (p ⁻¹' e.chartBall b ε), E))).map γ) =
          (FundamentalGroupoid.map (⟨Subtype.val, continuous_subtype_val⟩ :
              C(_root_.TopCat.of (e.chartBall b ε), B))).map
            ((FundamentalGroupoid.map (chartBallRestrict p e b ε)).map γ) := by
        induction γ using Quotient.ind
        rfl
      have h := (isoConstantOfHomotopy (X := _root_.TopCat.of (e.chartBall b ε))
        (e.chartBallContraction hb hε₀ hε)
        ((pullback (R := R) (⟨Subtype.val, continuous_subtype_val⟩ :
          C(_root_.TopCat.of (e.chartBall b ε), B))).obj L)).hom.naturality
        ((FundamentalGroupoid.map (chartBallRestrict p e b ε)).map γ)
      simp only [pullback_obj_map, constantFunctor_obj_map] at h ⊢
      rw [hγ]
      exact h)

variable [T1Space B]

/-- **The homology of a Serre fibration modulo the complement of a fibre, with coefficients from
the base, is the shifted homology of the fibre.** Let `p : E ⟶ B` be a Serre fibration over a `T₁`
space, `L` a local coefficient system on `B`, and `b` a point in the source of an open partial
homeomorphism `e : B → V` to a real normed space of finite dimension `r`. Then
`Hₘ(E, E ∖ p⁻¹(b); p*L) ≅ Hₙ(p⁻¹(b); L_b)` for `m = n + r`.

The isomorphism depends on `e` and on a ball of radius `ε` about `e b` inside the target of `e`:
the restriction of `L` to the corresponding chart ball is identified with the constant system at
`L_b` along its contraction onto `b`, and the resulting identification
`Hₘ(E, E ∖ p⁻¹(b); p*L) ≅ Hₘ(E, E ∖ p⁻¹(b); L_b)` is followed by
`TauCeti.TopCat.singularHomologyComplFiberIso`. -/
def twistedHomologyComplFiberIso (hp : serreFibrations p) (n m : ℕ) (h : n + finrank ℝ V = m)
    [FiniteDimensional ℝ V] :
    (TopPair.ofSubset (p ⁻¹' {b})ᶜ).twistedHomology ((pullback p.hom).obj L) m ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
        (L.obj (FundamentalGroupoid.mk b))).obj (_root_.TopCat.of (p ⁻¹' {b})) :=
  TopPair.twistedHomologyComplIso _ _ ((e.isOpen_chartBall b ε).preimage p.hom.continuous)
      ((isClosed_singleton.preimage p.hom.continuous).closure_subset.trans
        (preimage_mono (singleton_subset_iff.2 (e.mem_chartBall_self hb hε₀))))
      (chartBallCoefficientIso L e hb hε₀ hε) m ≪≫
    singularHomologyComplFiberIso _ e hb hε hε₀ hp n m h

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
    (TopPair.twistedHomologyComplIso _ _ ((e.isOpen_chartBall b ε).preimage p.hom.continuous)
      ((isClosed_singleton.preimage p.hom.continuous).closure_subset.trans
        (preimage_mono (singleton_subset_iff.2 (e.mem_chartBall_self hb hε₀))))
      (chartBallCoefficientIso L e hb hε₀ hε) m)

/-- A class `α ∈ Hₘ(E; p*L)` is detected by the shriek map
`Hₘ(E; p*L) → Hₘ(E, E ∖ p⁻¹(b); p*L) ≅ Hₙ(p⁻¹(b); L_b)` of the inclusion of `b`, for
`m = n + dim V`, exactly when its localization along the fibre is nonzero. In particular whether
it is detected does not depend on the chart. -/
theorem twistedHomologyπ_comp_twistedHomologyComplFiberIso_hom_ne_zero_iff
    [FiniteDimensional ℝ V] (hp : serreFibrations p) (n m : ℕ) (h : n + finrank ℝ V = m)
    (α : ((pullback p.hom).obj L).twistedHomology m) :
    ((TopPair.ofSubset (p ⁻¹' {b})ᶜ).twistedHomologyπ _ m ≫
        (twistedHomologyComplFiberIso L e hb hε₀ hε hp n m h).hom).hom α ≠ 0 ↔
      ((TopPair.ofSubset (p ⁻¹' {b})ᶜ).twistedHomologyπ _ m).hom α ≠ 0 :=
  not_congr (twistedHomologyComplFiberIso L e hb hε₀ hε hp n m h).toLinearEquiv.map_eq_zero_iff

/-- For a constant system `M` on `B`, the isomorphism
`TauCeti.TopCat.twistedHomologyComplFiberIso` is the comparison of twisted homology with constant
coefficients and ordinary homology, followed by the untwisted
`TauCeti.TopCat.singularHomologyComplFiberIso`. -/
lemma twistedHomologyComplFiberIso_hom_constant [FiniteDimensional ℝ V] (M : ModuleCat.{u} R)
    (hp : serreFibrations p) (n m : ℕ) (h : n + finrank ℝ V = m) :
    (twistedHomologyComplFiberIso ((constantFunctor B).obj M) e hb hε₀ hε hp n m h).hom =
      (TopPair.ofSubset (p ⁻¹' {b})ᶜ).twistedHomologyCoefficientMap
          (pullbackConstantIso p.hom M).hom m ≫
        ((TopPair.ofSubset (p ⁻¹' {b})ᶜ).twistedHomologyConstantIso M m).hom ≫
          (singularHomologyComplFiberIso M e hb hε hε₀ hp n m h).hom := by
  have hcoef : chartBallCoefficientIso ((constantFunctor B).obj M) e hb hε₀ hε =
      (pullback _).mapIso (pullbackConstantIso p.hom M) ≪≫ pullbackConstantIso _ M := by
    refine Iso.ext (NatTrans.ext (funext fun x ↦ ?_))
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.mapIso_hom, pullback_map_app,
      pullbackConstantIso_hom_app]
    -- At `x`, `chartBallCoefficientIso` is transport in the constant system `M`.
    exact (isoConstantOfHomotopy_hom_app _ _ _).trans
      (by erw [pullback_obj_map, constantFunctor_obj_map, Category.comp_id])
  rw [twistedHomologyComplFiberIso, Iso.trans_hom, hcoef]
  -- The ambient space of `(E, E ∖ p⁻¹(b))` is `E` only up to unfolding `TopPair.ofSubset`.
  erw [TopPair.twistedHomologyComplIso_hom_of_iso]
  exact Category.assoc _ _ _

end TopCat

end TauCeti
