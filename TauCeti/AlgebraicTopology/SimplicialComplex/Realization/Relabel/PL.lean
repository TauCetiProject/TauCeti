/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Relabel.Coordinates
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.PL

/-!
# Descending PL maps through vertex relabelings

A map between injectively relabeled polyhedra with a PL ambient coordinate formula
induces a map between the original polyhedra with a PL coordinate formula.
Extend the input by zero, apply the given formula, and restrict the output coordinates.
For a homeomorphism, applying the same result to its inverse transports the inverse
PL formula as well.

This removes the auxiliary vertex labels used to compare polyhedra by stellar moves,
so that their PL identifications can be used on the original sphere and ball links.
The polyhedra may lie in arbitrary containing weak realizations. No finiteness,
compactness, or global comparison with the coordinate topology is required, and unused
ambient vertices contribute no points.

The same coordinate transport realizes a `PLHomeomorphic` relation inside arbitrary ambient
complexes, or as a homeomorphism to the full realization of its target complex. These forms are
the interface used to transport standard PL charts to a subpolyhedron.

The coordinate transport uses `relabelingHomeomorph` and its extension and restriction
formulas, together with `TauCeti.IsPLOn.comp`.

Reference: C. P. Rourke and B. J. Sanderson, *Introduction to Piecewise-Linear Topology*,
Chapters 1–2.
-/

public section

open Set Function TauCeti

namespace PreAbstractSimplicialComplex

open AbstractSimplicialComplex

variable {α β κ ν : Type*} [DecidableEq κ] [DecidableEq ν]
  {K : AbstractSimplicialComplex α} {L : AbstractSimplicialComplex β}
  {A : AbstractSimplicialComplex κ} {B : AbstractSimplicialComplex ν}
  (P : PreAbstractSimplicialComplex α) (Q : PreAbstractSimplicialComplex β)
  (e : α ↪ κ) (d : β ↪ ν)
  (hK : P ≤ K.toPreAbstractSimplicialComplex)
  (hL : Q ≤ L.toPreAbstractSimplicialComplex)
  (hA : P.map e ≤ A.toPreAbstractSimplicialComplex)
  (hB : Q.map d ≤ B.toPreAbstractSimplicialComplex)

/-- A PL coordinate formula for a map of relabeled polyhedra descends to
the original polyhedra. Its explicit formula extends the input coordinates by zero
and restricts the output coordinates. For a homeomorphism, use the theorem with its
inverse and the two relabelings exchanged to descend the inverse formula. -/
theorem isPLOn_restriction_comp_extendByZero
    (h : {x : Realization A // x.1.support ∈ P.map e} →
      {y : Realization B // y.1.support ∈ Q.map d})
    (f : (κ → ℝ) → (ν → ℝ))
    (hf : IsPLOn f
      (range (fun x : {x : Realization A // x.1.support ∈ P.map e} => (x.1.1 : κ → ℝ))))
    (hcoord : ∀ x : {x : Realization A // x.1.support ∈ P.map e},
      f (x.1.1 : κ → ℝ) = (h x).1.1) :
    IsPLOn
        (Function.ExtendByZero.restriction ℝ d ∘ f ∘
          Function.ExtendByZero.continuousLinearMap ℝ e)
        (range (fun x : {x : Realization K // x.1.support ∈ P} => (x.1.1 : α → ℝ))) ∧
      ∀ x : {x : Realization K // x.1.support ∈ P},
        (Function.ExtendByZero.restriction ℝ d ∘ f ∘
          Function.ExtendByZero.continuousLinearMap ℝ e) (x.1.1 : α → ℝ) =
            (((Q.relabelingHomeomorph d hL hB).symm ∘ h ∘
              P.relabelingHomeomorph e hK hA) x).1.1 := by
  have hmap : MapsTo (Function.ExtendByZero.continuousLinearMap ℝ e)
      (range (fun x : {x : Realization K // x.1.support ∈ P} => (x.1.1 : α → ℝ)))
      (range (fun x : {x : Realization A // x.1.support ∈ P.map e} => (x.1.1 : κ → ℝ))) := by
    rw [P.range_coe_map_eq_image_extendByZero e hK hA]
    exact mapsTo_image _ _
  refine ⟨(isPLOn_continuousAffineMap
    (Function.ExtendByZero.restriction ℝ d).toContinuousAffineMap univ).comp
      (hf.comp (isPLOn_continuousAffineMap
        (Function.ExtendByZero.continuousLinearMap ℝ e).toContinuousAffineMap _) hmap)
      (fun _ _ => mem_univ _), ?_⟩
  intro x
  simp only [Function.comp_apply,
    ← relabelingHomeomorph_coe_eq_extendByZero P e hK hA x,
    hcoord, relabelingHomeomorph_symm_coe_eq_restriction]

/-- A PL homeomorphism after two injective relabelings descends to a PL homeomorphism before
relabeling. The two complexes may use different embeddings into the common target vertex type.

The descended coordinate formulas extend the input by zero along the source embedding, apply the
given formula, and restrict along the target embedding. -/
theorem PLHomeomorphic.of_common_relabeling
    {A B : PreAbstractSimplicialComplex α} {e d : α ↪ κ}
    (h : PLHomeomorphic (A.map e) (B.map d)) : PLHomeomorphic A B := by
  obtain ⟨φ, f, g, hf, hg, hφ, hφinv⟩ := plHomeomorphic_iff.mp h
  let rA := A.relabelingHomeomorph e (le_top _) (le_top _)
  let rB := B.relabelingHomeomorph d (le_top _) (le_top _)
  let ψ := rA.trans (φ.trans rB.symm)
  let f' : (α → ℝ) → (α → ℝ) :=
    Function.ExtendByZero.restriction ℝ d ∘ f ∘
      Function.ExtendByZero.continuousLinearMap ℝ e
  let g' : (α → ℝ) → (α → ℝ) :=
    Function.ExtendByZero.restriction ℝ e ∘ g ∘
      Function.ExtendByZero.continuousLinearMap ℝ d
  have hf' := isPLOn_restriction_comp_extendByZero A B e d
    (le_top _) (le_top _) (le_top _) (le_top _) φ f hf hφ
  have hg' := isPLOn_restriction_comp_extendByZero B A d e
    (le_top _) (le_top _) (le_top _) (le_top _) φ.symm g hg hφinv
  refine PLHomeomorphic.intro ψ f' g' hf'.1 hg'.1 ?_ ?_
  · intro x
    simpa only [ψ, rA, rB, f', Function.comp_apply, Homeomorph.trans_apply] using hf'.2 x
  · intro y
    simpa only [ψ, rA, rB, g', Function.comp_apply, Homeomorph.symm_trans_apply,
      Homeomorph.symm_symm] using hg'.2 y

/-- Injectively relabeling the vertices of a complex does not change its PL homeomorphism type.

The forward ambient formula extends barycentric coordinates by zero; the inverse formula
restricts them to the original vertex labels. -/
theorem PLHomeomorphic.relabeling {γ δ : Type*} [DecidableEq δ]
    (P : PreAbstractSimplicialComplex γ) (e : γ ↪ δ) :
    PLHomeomorphic P (P.map e) := by
  let r := P.relabelingHomeomorph e (le_top P) (le_top (P.map e))
  let f : (γ → ℝ) → (δ → ℝ) := Function.ExtendByZero.continuousLinearMap ℝ e
  let g : (δ → ℝ) → (γ → ℝ) := Function.ExtendByZero.restriction ℝ e
  refine PLHomeomorphic.intro r f g
    (isPLOn_continuousAffineMap
      (Function.ExtendByZero.continuousLinearMap ℝ e).toContinuousAffineMap _)
    (isPLOn_continuousAffineMap
      (Function.ExtendByZero.restriction ℝ e).toContinuousAffineMap _) ?_ ?_
  · intro x
    simpa only [r, f] using (relabelingHomeomorph_coe_eq_extendByZero
      P e (le_top P) (le_top (P.map e)) x).symm
  · intro y
    simpa only [r, g] using (relabelingHomeomorph_symm_coe_eq_restriction
      P e (le_top P) (le_top (P.map e)) y).symm

/-- Realize a PL homeomorphism inside arbitrary ambient simplicial complexes containing its two
polyhedra. The coordinate formulas and their PL domains are transported unchanged. -/
theorem PLHomeomorphic.exists_homeomorph_ambient
    {γ δ : Type*}
    {P : PreAbstractSimplicialComplex γ} {Q : PreAbstractSimplicialComplex δ}
    {C : AbstractSimplicialComplex γ} {D : AbstractSimplicialComplex δ}
    (h : PLHomeomorphic P Q)
    (hP : P ≤ C.toPreAbstractSimplicialComplex)
    (hQ : Q ≤ D.toPreAbstractSimplicialComplex) :
    ∃ e : {x : Realization C // x.1.support ∈ P} ≃ₜ
        {y : Realization D // y.1.support ∈ Q},
      ∃ f : (γ → ℝ) → (δ → ℝ), ∃ g : (δ → ℝ) → (γ → ℝ),
        IsPLOn f (range fun x : {x : Realization C // x.1.support ∈ P} =>
          (x.1.1 : γ → ℝ)) ∧
        IsPLOn g (range fun y : {y : Realization D // y.1.support ∈ Q} =>
          (y.1.1 : δ → ℝ)) ∧
        (∀ x, f (x.1.1 : γ → ℝ) = (e x).1.1) ∧
        ∀ y, g (y.1.1 : δ → ℝ) = (e.symm y).1.1 := by
  classical
  obtain ⟨e, f, g, hf, hg, he, heinv⟩ := plHomeomorphic_iff.mp h
  let rP := topRealizationHomeomorph P hP
  let rQ := topRealizationHomeomorph Q hQ
  let ψ := rP.symm.trans (e.trans rQ)
  have hrP (x) : ((rP x).1.1 : γ → ℝ) = (x.1.1 : γ → ℝ) := by
    exact topRealizationHomeomorph_val P hP x
  have hrQ (y) : ((rQ y).1.1 : δ → ℝ) = (y.1.1 : δ → ℝ) := by
    exact topRealizationHomeomorph_val Q hQ y
  have hrangeP :
      range (fun x : {x : Realization C // x.1.support ∈ P} => (x.1.1 : γ → ℝ)) =
        realizedCoords P := by
    rw [← rP.surjective.range_comp]
    exact congrArg range (funext hrP)
  have hrangeQ :
      range (fun y : {y : Realization D // y.1.support ∈ Q} => (y.1.1 : δ → ℝ)) =
        realizedCoords Q := by
    rw [← rQ.surjective.range_comp]
    exact congrArg range (funext hrQ)
  refine ⟨ψ, f, g, hrangeP.symm ▸ hf, hrangeQ.symm ▸ hg, ?_, ?_⟩
  · intro x
    have hx : ((rP.symm x).1.1 : γ → ℝ) = (x.1.1 : γ → ℝ) := by
      rw [← hrP (rP.symm x), rP.apply_symm_apply]
    calc
      f (x.1.1 : γ → ℝ) = f ((rP.symm x).1.1 : γ → ℝ) := congrArg f hx.symm
      _ = ((e (rP.symm x)).1.1 : δ → ℝ) := he _
      _ = ((rQ (e (rP.symm x))).1.1 : δ → ℝ) := (hrQ _).symm
      _ = ((ψ x).1.1 : δ → ℝ) := rfl
  · intro y
    have hy : ((rQ.symm y).1.1 : δ → ℝ) = (y.1.1 : δ → ℝ) := by
      rw [← hrQ (rQ.symm y), rQ.apply_symm_apply]
    calc
      g (y.1.1 : δ → ℝ) = g ((rQ.symm y).1.1 : δ → ℝ) := congrArg g hy.symm
      _ = ((e.symm (rQ.symm y)).1.1 : γ → ℝ) := heinv _
      _ = ((rP (e.symm (rQ.symm y))).1.1 : γ → ℝ) := (hrP _).symm
      _ = ((ψ.symm y).1.1 : γ → ℝ) := rfl

/-- Realize the target of a PL homeomorphism as its full simplicial realization rather than as
the equivalent support-restricted subtype. -/
theorem PLHomeomorphic.exists_homeomorph_realization
    {γ δ : Type*}
    {P : PreAbstractSimplicialComplex γ} {C : AbstractSimplicialComplex γ}
    {D : AbstractSimplicialComplex δ}
    (h : PLHomeomorphic P D.toPreAbstractSimplicialComplex)
    (hP : P ≤ C.toPreAbstractSimplicialComplex) :
    ∃ e : {x : Realization C // x.1.support ∈ P} ≃ₜ Realization D,
      ∃ f : (γ → ℝ) → (δ → ℝ), ∃ g : (δ → ℝ) → (γ → ℝ),
        IsPLOn f (range fun x : {x : Realization C // x.1.support ∈ P} =>
          (x.1.1 : γ → ℝ)) ∧
        IsPLOn g (range fun y : Realization D => (y.1 : δ → ℝ)) ∧
        (∀ x, f (x.1.1 : γ → ℝ) = (e x).1) ∧
        ∀ y, g (y.1 : δ → ℝ) = (e.symm y).1.1 := by
  classical
  obtain ⟨e, f, g, hf, hg, he, heinv⟩ := h.exists_homeomorph_ambient hP le_rfl
  let S : Set (Realization D) := {y | y.1.support ∈ D.toPreAbstractSimplicialComplex}
  have hS : S = Set.univ := Set.eq_univ_of_forall fun y => support_mem D y
  let u : S ≃ₜ Realization D := (Homeomorph.setCongr hS).trans (Homeomorph.Set.univ _)
  let ψ := e.trans u
  have hu (y : S) : ((u y).1 : δ → ℝ) = (y.1.1 : δ → ℝ) := by
    simp [u]
  have hrange :
      range (fun y : Realization D => (y.1 : δ → ℝ)) =
        range (fun y : S => (y.1.1 : δ → ℝ)) := by
    rw [← u.surjective.range_comp]
    exact congrArg range (funext hu)
  refine ⟨ψ, f, g, hf, hrange.symm ▸ hg, ?_, ?_⟩
  · intro x
    rw [he]
    exact (hu (e x)).symm
  · intro y
    have hy : ((u.symm y).1.1 : δ → ℝ) = (y.1 : δ → ℝ) := by
      rw [← hu (u.symm y), u.apply_symm_apply]
    rw [← hy, heinv]
    rfl

end PreAbstractSimplicialComplex
