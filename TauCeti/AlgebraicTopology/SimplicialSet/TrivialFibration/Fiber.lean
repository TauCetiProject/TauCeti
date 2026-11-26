/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Cylinder
public import TauCeti.AlgebraicTopology.SimplicialSet.Fiber
public import TauCeti.AlgebraicTopology.SimplicialSet.Horn
public import TauCeti.AlgebraicTopology.SimplicialSet.TrivialFibration
public import TauCeti.AlgebraicTopology.SimplicialSet.WeaklyContractible

/-!
# Trivial fibrations are the Kan fibrations with contractible fibres

A morphism of simplicial sets with the right lifting property with respect to all monomorphisms
(a trivial fibration of the Kan–Quillen model structure) is a Kan fibration whose fibres
`SSet.fiber p y` over the vertices `y` of the base are weakly contractible
(`SSet.IsWeaklyContractible`). Conversely, a Kan fibration whose fibres are weakly contractible
is a trivial fibration. The fibres of a Kan fibration are Kan complexes, for which weak
contractibility is contractibility, so being a trivial fibration is a condition on the fibres of
a Kan fibration, one vertex of the base at a time. This reduces the proof that a Kan fibration
which is a weak equivalence is a trivial fibration to the contractibility of its fibres.

The case of a map to a point comes first: a map from `K` to a terminal simplicial set is a trivial
fibration exactly when `K` is a weakly contractible Kan complex
(`SSet.rlp_monomorphisms_iff_kanComplex_and_isWeaklyContractible_of_isTerminal`). Over a point, a
shrinking in the sense of `TauCeti/AlgebraicTopology/SimplicialSet/TrivialFibration.lean` is a
homotopy from a constant map to the identity.

For a Kan fibration `p` with weakly contractible fibres it suffices to lift against the boundary
inclusions `∂Δ[n] ⟶ Δ[n]`. Given a square from `∂Δ[n] ⟶ Δ[n]` to `p` with top map `a` and bottom
map `b`, let `y` be the image under `b` of the initial vertex, and compose the contraction of
`Δ[n]` onto its initial vertex (`SSet.stdSimplex.contraction`) with `b`.

* Over the boundary, lift this homotopy backwards from `a`; its other end lies in the fibre over
  `y`.
* That end is a map from `∂Δ[n]` to the contractible fibre, so it extends to `Δ[n]`.
* Lift the homotopy over all of `Δ[n]`, extending these two lifts
  (`SSet.exists_lift_cylinder_ι₀_of_mono`). Its end over `1` solves the lifting problem.

## Main results

* `SSet.rlp_monomorphisms_iff_kanComplex_and_isWeaklyContractible_of_isTerminal`: a map to a
  terminal simplicial set is a trivial fibration exactly when its source is a weakly
  contractible Kan complex.
* `SSet.rlp_monomorphisms_of_isWeaklyContractible_fiber`: a Kan fibration whose fibres are weakly
  contractible is a trivial fibration.
* `SSet.rlp_monomorphisms_iff_fibration_and_isWeaklyContractible_fiber`: the resulting
  characterization of trivial fibrations.

## References

* P. G. Goerss and J. F. Jardine, *Simplicial homotopy theory*, Progress in Mathematics 174,
  Birkhäuser, 1999, Chapter I.
* P. Gabriel and M. Zisman, *Calculus of fractions and homotopy theory*, Ergebnisse der
  Mathematik 35, Springer, 1967, Chapter IV.
-/

public section

universe u

open CategoryTheory Limits MorphismProperty MonoidalCategory CartesianMonoidalCategory
  HomotopicalAlgebra Simplicial

namespace SSet

open modelCategoryQuillen

variable {X Y : SSet.{u}}

/-- A map `p : K ⟶ T` to a terminal simplicial set has the right lifting property with respect to
all monomorphisms (it is a trivial fibration) if and only if `K` is a weakly contractible Kan
complex. -/
theorem rlp_monomorphisms_iff_kanComplex_and_isWeaklyContractible_of_isTerminal
    {K T : SSet.{u}} (hT : IsTerminal T) (p : K ⟶ T) :
    (monomorphisms SSet.{u}).rlp p ↔ KanComplex K ∧ IsWeaklyContractible K := by
  rw [rlp_monomorphisms_iff, ← isFibrant_iff_of_isTerminal p hT]
  refine and_congr_right fun _ ↦ ⟨fun ⟨h⟩ ↦ ?_, fun _ ↦ ?_⟩
  · -- Over a point, the shrinking is a homotopy from a constant map to the identity.
    let t : T _⦋0⦌ := yonedaEquiv (hT.from Δ[0])
    have e : p ≫ h.section_ = const (h.section_.app _ t) :=
      (congrArg (· ≫ h.section_) (hT.hom_ext p (const t))).trans (const_comp _ _)
    exact .of_homotopy (.mk' h.homotopy.h (by rw [h.homotopy.h₀, e]) h.homotopy.h₁)
  · -- Conversely, a homotopy from a constant map to the identity is a shrinking over a point.
    obtain ⟨x, ⟨H⟩⟩ := IsWeaklyContractible.exists_homotopy_const (𝟙 K)
    exact ⟨{ section_ := const x
             section_comp := hT.hom_ext _ _
             homotopy := .mk' H.h (by rw [H.h₀, comp_const]) H.h₁
             homotopy_h_comp := hT.hom_ext _ _ }⟩

/-- A Kan fibration whose fibres over all vertices of the base are weakly contractible has the
right lifting property with respect to all monomorphisms: it is a trivial fibration. -/
theorem rlp_monomorphisms_of_isWeaklyContractible_fiber (p : X ⟶ Y) [Fibration p]
    (hp : ∀ y : Y _⦋0⦌, IsWeaklyContractible (fiber p y : SSet.{u})) :
    (monomorphisms SSet.{u}).rlp p := by
  rw [SSet.rlp_monomorphisms]
  refine fun _ _ _ ⟨n⟩ ↦ ⟨fun {a b} sq ↦ ?_⟩
  -- Contract `Δ[n]` onto its initial vertex, over `Y` through `b`; the vertex lies over `y`.
  let C := stdSimplex.contraction.{u} n
  let y : Y _⦋0⦌ := b.app _ (stdSimplex.obj₀Equiv.symm 0)
  have hC₀ : ι₀ ≫ C.h ≫ b = const y := by rw [C.h₀_assoc, const_comp]
  -- Over the boundary, lift the contraction backwards from `a`, ending in the fibre over `y`.
  have := anodyneExtensions_ι₁ (∂Δ[n] : SSet.{u}) p (mem_fibrations p)
  have sq₁ : CommSq a ι₁ p (∂Δ[n].ι ▷ Δ[1] ≫ C.h ≫ b) :=
    ⟨by rw [ι₁_comp_assoc, C.h₁_assoc, Category.id_comp, sq.w]⟩
  let L₁ := sq₁.lift
  have hL₁ : (ι₀ ≫ L₁) ≫ p = const y := by
    rw [Category.assoc, sq₁.fac_right, ι₀_comp_assoc, hC₀, comp_const]
  -- The fibre over `y` is a contractible Kan complex, so the end of `L₁` extends to `Δ[n]`.
  have hF := (rlp_monomorphisms_iff_kanComplex_and_isWeaklyContractible_of_isTerminal
    stdSimplex.isTerminalObj₀ (stdSimplex.isTerminalObj₀.from (fiber p y : SSet.{u}))).2
      ⟨inferInstance, hp y⟩ _ (monomorphisms.infer_property ∂Δ[n].ι)
  have sqF : CommSq (Subcomplex.lift (ι₀ ≫ L₁) ((range_le_fiber_iff _ p y).2 hL₁)) ∂Δ[n].ι
      (stdSimplex.isTerminalObj₀.from (fiber p y : SSet.{u})) (stdSimplex.isTerminalObj₀.from _) :=
    ⟨stdSimplex.isTerminalObj₀.hom_ext _ _⟩
  let g := sqF.lift ≫ (fiber p y).ι
  have hg : ∂Δ[n].ι ≫ g = ι₀ ≫ L₁ := by
    simp only [g, sqF.fac_left_assoc, Subcomplex.lift_ι]
  have hgp : g ≫ p = const y := by
    have := (range_le_fiber_iff (fiber p y).ι p y).1 (by simp)
    simp [g, this]
  -- Lift the contraction over `Δ[n]`, prescribed by `L₁` on the boundary and by `g` over `0`.
  obtain ⟨L, -, hL, hLp⟩ := exists_lift_cylinder_ι₀_of_mono ∂Δ[n].ι p (C.h ≫ b) g L₁
    (by rw [hgp, hC₀]) sq₁.fac_right hg
  -- Its end over `1` lies over `b` and extends `a`.
  exact ⟨⟨⟨ι₁ ≫ L, by rw [← ι₁_comp_assoc, hL, sq₁.fac_left],
    by rw [Category.assoc, hLp, C.h₁_assoc, Category.id_comp]⟩⟩⟩

/-- A morphism of simplicial sets has the right lifting property with respect to all monomorphisms
(it is a trivial fibration) if and only if it is a Kan fibration whose fibres over all vertices of
the base are weakly contractible. -/
theorem rlp_monomorphisms_iff_fibration_and_isWeaklyContractible_fiber {p : X ⟶ Y} :
    (monomorphisms SSet.{u}).rlp p ↔
      Fibration p ∧ ∀ y : Y _⦋0⦌, IsWeaklyContractible (fiber p y : SSet.{u}) := by
  refine ⟨fun hp ↦ ⟨(rlp_monomorphisms_iff.1 hp).1, fun y ↦ ?_⟩,
    fun ⟨_, h⟩ ↦ rlp_monomorphisms_of_isWeaklyContractible_fiber p h⟩
  -- The fibre over `y` is the restriction of `p` over the terminal subcomplex generated by `y`,
  -- which inherits the lifting properties of `p`.
  have : (monomorphisms SSet.{u}).rlp ((Subcomplex.ofSimplex y).fromPreimage p) :=
    fun _ _ i hi ↦ have := hp i hi; inferInstance
  rw [fiber_eq_preimage]
  exact ((rlp_monomorphisms_iff_kanComplex_and_isWeaklyContractible_of_isTerminal
    (Subcomplex.isTerminalOfSimplex y) _).1 this).2

end SSet
