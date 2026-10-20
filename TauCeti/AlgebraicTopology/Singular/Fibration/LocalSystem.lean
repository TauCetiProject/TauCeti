/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.HomotopyInvariance
public import TauCeti.Topology.Homotopy.HurewiczFibration.Transport

/-!
# The local system of fibre homology of a Hurewicz fibration

For a Hurewicz fibration `p : E → B` the homology groups `H_t(p⁻¹ b)` of the fibres, computed with
normalized cubical chains, form a local coefficient system on `B`
(`TauCeti.fibreLocalSystem`): a path `γ` from `b₀` to `b₁` acts by the map induced by the
transport `p⁻¹ b₀ → p⁻¹ b₁` along `γ` (`TauCeti.LiftingFunction.transport`).  The transport
depends on the path only up to homotopy and is functorial up to homotopy
(`TauCeti.LiftingFunction.transport_homotopic`, `TauCeti.LiftingFunction.transport_refl_homotopic`,
`TauCeti.LiftingFunction.transport_trans_homotopic`), and homotopic maps induce the same map on
homology, so the action factors through the fundamental groupoid and is functorial.

## Main definitions

* `TauCeti.fibreTransport Λ γ`: the transport along `γ` as a map of fibres in `TopCat`.
* `TauCeti.fibreLocalSystem Λ k t`: the local system `b ↦ H_t(p⁻¹ b; k)`.

## Main results

* `TauCeti.fibreLocalSystem_obj`, `TauCeti.fibreLocalSystem_map_mk`: the value of the local system
  on an object and on the class of a path.

## References

* A. Hatcher, *Algebraic Topology*, Section 4.2 and Section 3.H.
-/

public section

noncomputable section

open CategoryTheory

universe u

namespace TauCeti

variable {E B : TopCat.{u}} {p : E ⟶ B} (Λ : LiftingFunction p.hom)

/-- The transport in the fibres of a Hurewicz fibration along a path, as a morphism of `TopCat`. -/
def fibreTransport {b₀ b₁ : B} (γ : Path b₀ b₁) : p.fiber b₀ ⟶ p.fiber b₁ :=
  TopCat.ofHom (Λ.transport γ)

theorem fibreTransport_apply_coe {b₀ b₁ : B} (γ : Path b₀ b₁) (x : p.fiber b₀) :
    (fibreTransport Λ γ x).1 = (Λ.transport γ x).1 :=
  (rfl)

variable (k : Type u) [Ring k]

/-- Homotopic paths have the same induced map on the homology of the fibres. -/
theorem homologyMap_fibreTransport_congr {b₀ b₁ : B} {γ γ' : Path b₀ b₁} (h : γ.Homotopic γ')
    (t : ℕ) :
    HomologicalComplex.homologyMap ((normalizedCubicalChainComplex k).map (fibreTransport Λ γ)) t
      = HomologicalComplex.homologyMap
        ((normalizedCubicalChainComplex k).map (fibreTransport Λ γ')) t := by
  obtain ⟨H⟩ := Λ.transport_homotopic h
  exact TopCat.Homotopy.congr_homologyMap_normalizedCubicalChainComplex (k := k) H t

/-- The **local system of fibre homology** `b ↦ H_t(p⁻¹ b; k)` of a Hurewicz fibration with
lifting function `Λ`, with normalized cubical chains. -/
@[expose] def fibreLocalSystem (t : ℕ) : LocalCoefficientSystem.{u, u, u} k B where
  obj b := ((normalizedCubicalChainComplex k).obj (p.fiber b.as)).homology t
  map {b₀ b₁} := Quotient.lift
    (fun γ ↦ HomologicalComplex.homologyMap
      ((normalizedCubicalChainComplex k).map (fibreTransport Λ γ)) t)
    (fun _ _ h ↦ homologyMap_fibreTransport_congr Λ k h t)
  map_id b := by
    obtain ⟨H⟩ := Λ.transport_refl_homotopic b.as
    exact (TopCat.Homotopy.congr_homologyMap_normalizedCubicalChainComplex (k := k)
      (g := 𝟙 _) H t).trans (by simp)
  map_comp f g := by
    induction f using Path.Homotopic.Quotient.ind with | mk γ =>
    induction g using Path.Homotopic.Quotient.ind with | mk δ =>
    obtain ⟨H⟩ := Λ.transport_trans_homotopic γ δ
    exact (TopCat.Homotopy.congr_homologyMap_normalizedCubicalChainComplex (k := k)
      (g := fibreTransport Λ γ ≫ fibreTransport Λ δ) H t).trans
      (by rw [Functor.map_comp, HomologicalComplex.homologyMap_comp]; rfl)

theorem fibreLocalSystem_obj (t : ℕ) (b : FundamentalGroupoid B) :
    (fibreLocalSystem Λ k t).obj b =
      ((normalizedCubicalChainComplex k).obj (p.fiber b.as)).homology t :=
  (rfl)

theorem fibreLocalSystem_map_mk (t : ℕ) {b₀ b₁ : FundamentalGroupoid B}
    (γ : Path b₀.as b₁.as) :
    (fibreLocalSystem Λ k t).map (Path.Homotopic.Quotient.mk γ) =
      HomologicalComplex.homologyMap
        ((normalizedCubicalChainComplex k).map (fibreTransport Λ γ)) t :=
  (rfl)

end TauCeti
