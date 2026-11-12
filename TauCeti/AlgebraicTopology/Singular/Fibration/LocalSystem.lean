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
# The local system of fiber homology of a Hurewicz fibration

For a Hurewicz fibration `p : E → B` the homology groups `H_t(p⁻¹ b)` of the fibers, computed with
normalized cubical chains, form a local coefficient system on `B`
(`TauCeti.fiberLocalSystem`): a path `γ` from `b₀` to `b₁` acts by the map induced by the
transport `p⁻¹ b₀ → p⁻¹ b₁` along `γ` (`TauCeti.LiftingFunction.transport`).

## Main definitions

* `TauCeti.fiberTransport Λ γ`: the transport along `γ` as a map of fibers in `TopCat`.
* `TauCeti.fiberLocalSystem Λ k t`: the local system `b ↦ H_t(p⁻¹ b; k)`.
* `TauCeti.fiberLocalSystemObjIso`: its value at a point is the homology of the fiber.

## Main results

* `TauCeti.fiberLocalSystem_map_mk`: the local system sends the class of a path to the map induced
  by the transport along it.

## References

* A. Hatcher, *Algebraic Topology*, Section 4.2 and Section 3.H.
-/

public section

noncomputable section

open CategoryTheory

universe u

namespace TauCeti

variable {E B : TopCat.{u}} {p : E ⟶ B} (Λ : LiftingFunction p.hom)

/-- The transport in the fibers of a Hurewicz fibration along a path, as a morphism of `TopCat`. -/
def fiberTransport {b₀ b₁ : B} (γ : Path b₀ b₁) : p.fiber b₀ ⟶ p.fiber b₁ :=
  TopCat.ofHom (Λ.transport γ)

/-- The underlying continuous map of the fiber transport is the transport. -/
@[simp]
theorem fiberTransport_hom {b₀ b₁ : B} (γ : Path b₀ b₁) :
    (fiberTransport Λ γ).hom = Λ.transport γ :=
  (rfl)

variable (k : Type u) [Ring k]

/-- Homotopic paths have the same induced map on the homology of the fibers. -/
theorem homologyMap_fiberTransport_congr {b₀ b₁ : B} {γ γ' : Path b₀ b₁} (h : γ.Homotopic γ')
    (t : ℕ) :
    HomologicalComplex.homologyMap ((normalizedCubicalChainComplex k).map (fiberTransport Λ γ)) t
      = HomologicalComplex.homologyMap
        ((normalizedCubicalChainComplex k).map (fiberTransport Λ γ')) t := by
  obtain ⟨H⟩ := Λ.transport_homotopic h
  exact TopCat.Homotopy.congr_homologyMap_normalizedCubicalChainComplex (k := k) H t

/-- Transport along a constant path induces the identity on the homology of the fiber. -/
theorem homologyMap_fiberTransport_refl (b : B) (t : ℕ) :
    HomologicalComplex.homologyMap
      ((normalizedCubicalChainComplex k).map (fiberTransport Λ (Path.refl b))) t = 𝟙 _ := by
  have h : (fiberTransport Λ (Path.refl b)).hom.Homotopic (TopCat.Hom.hom (𝟙 (p.fiber b))) := by
    rw [fiberTransport_hom, TopCat.hom_id]
    exact Λ.transport_refl_homotopic b
  obtain ⟨H⟩ := h
  -- `TopCat.Homotopy` is by definition a homotopy of the underlying continuous maps.
  rw [TopCat.Homotopy.congr_homologyMap_normalizedCubicalChainComplex (k := k) (g := 𝟙 _) H t,
    CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id]

/-- Transport along a concatenation induces the composite on the homology of the fibers. -/
theorem homologyMap_fiberTransport_trans {b₀ b₁ b₂ : B} (γ : Path b₀ b₁) (δ : Path b₁ b₂)
    (t : ℕ) :
    HomologicalComplex.homologyMap
        ((normalizedCubicalChainComplex k).map (fiberTransport Λ (γ.trans δ))) t =
      HomologicalComplex.homologyMap
          ((normalizedCubicalChainComplex k).map (fiberTransport Λ γ)) t ≫
        HomologicalComplex.homologyMap
          ((normalizedCubicalChainComplex k).map (fiberTransport Λ δ)) t := by
  have h : (fiberTransport Λ (γ.trans δ)).hom.Homotopic
      (fiberTransport Λ γ ≫ fiberTransport Λ δ).hom := by
    rw [TopCat.hom_comp, fiberTransport_hom, fiberTransport_hom, fiberTransport_hom]
    exact Λ.transport_trans_homotopic γ δ
  obtain ⟨H⟩ := h
  -- `TopCat.Homotopy` is by definition a homotopy of the underlying continuous maps.
  rw [TopCat.Homotopy.congr_homologyMap_normalizedCubicalChainComplex (k := k)
    (g := fiberTransport Λ γ ≫ fiberTransport Λ δ) H t, CategoryTheory.Functor.map_comp,
    HomologicalComplex.homologyMap_comp]

/-- The **local system of fiber homology** `b ↦ H_t(p⁻¹ b; k)` of a Hurewicz fibration with
lifting function `Λ`, with normalized cubical chains. -/
def fiberLocalSystem (t : ℕ) : LocalCoefficientSystem.{u, u, u} k B where
  obj b := ((normalizedCubicalChainComplex k).obj (p.fiber b.as)).homology t
  map {b₀ b₁} := Quotient.lift
    (fun γ ↦ HomologicalComplex.homologyMap
      ((normalizedCubicalChainComplex k).map (fiberTransport Λ γ)) t)
    (fun _ _ h ↦ homologyMap_fiberTransport_congr Λ k h t)
  -- The identity of the fundamental groupoid is the class of the constant path
  -- (`FundamentalGroupoid.id_eq_path_refl`).
  map_id b := homologyMap_fiberTransport_refl Λ k b.as t
  -- Composition in the fundamental groupoid is the class of the concatenation
  -- (`FundamentalGroupoid.comp_eq`), on which `Quotient.lift` evaluates by definition.
  map_comp f g := by
    induction f using Path.Homotopic.Quotient.ind with | mk γ =>
    induction g using Path.Homotopic.Quotient.ind with | mk δ =>
    exact homologyMap_fiberTransport_trans Λ k γ δ t

/-- The value of the local system at a point is the homology of the fiber over it. -/
def fiberLocalSystemObjIso (t : ℕ) (b : FundamentalGroupoid B) :
    (fiberLocalSystem Λ k t).obj b ≅
      ((normalizedCubicalChainComplex k).obj (p.fiber b.as)).homology t :=
  Iso.refl _

/-- The local system sends the class of a path to the map induced on homology by the transport
along the path. -/
theorem fiberLocalSystem_map_mk (t : ℕ) {b₀ b₁ : FundamentalGroupoid B}
    (γ : Path b₀.as b₁.as) :
    (fiberLocalSystem Λ k t).map (Path.Homotopic.Quotient.mk γ) =
      (fiberLocalSystemObjIso Λ k t b₀).hom ≫
        HomologicalComplex.homologyMap
          ((normalizedCubicalChainComplex k).map (fiberTransport Λ γ)) t ≫
        (fiberLocalSystemObjIso Λ k t b₁).inv := by
  simp only [fiberLocalSystemObjIso, Iso.refl_hom, Iso.refl_inv]
  -- `Quotient.lift` evaluates on the class of a path by definition.
  rfl

end TauCeti
