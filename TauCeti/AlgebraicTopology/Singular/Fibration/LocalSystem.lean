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
* `TauCeti.fiberLocalSystemObjIso`, `TauCeti.fiberLocalSystemSingularObjIso`: its value at a point,
  identified with the cubical or simplicial singular homology of the fiber.
* `CategoryTheory.CommSq.fiberLocalSystemMap`: the morphism of fiber local systems induced by a
  commutative square of fibrations, an isomorphism when each fiber map is an isomorphism.

## Main results

* `TauCeti.fiberLocalSystem_eq`: the local system does not depend on the choice of lifting function.
* `TauCeti.fiberLocalSystem_map_mk`, `TauCeti.fiberLocalSystem_map_mk_singular`: the local system
  sends the class of a path to the map induced by the transport along it on cubical or simplicial
  singular homology.

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

/-- **Independence of the lifting function.** Two lifting functions for the same fibration induce
equal local systems of fiber homology. -/
theorem fiberLocalSystem_eq (Λ' : LiftingFunction p.hom) (t : ℕ) :
    fiberLocalSystem Λ k t = fiberLocalSystem Λ' k t := by
  unfold fiberLocalSystem
  congr 1
  funext b₀ b₁ q
  induction q using Path.Homotopic.Quotient.ind with | mk γ =>
  obtain ⟨H⟩ := Λ.transport_homotopic_of_liftingFunction Λ' γ
  exact TopCat.Homotopy.congr_homologyMap_normalizedCubicalChainComplex (k := k)
    (f := fiberTransport Λ γ) (g := fiberTransport Λ' γ) H t

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

/-- The value of the fiber local system at a point, identified with the simplicial singular
homology of the fiber via `TauCeti.singularCubicalHomologyIso`. -/
def fiberLocalSystemSingularObjIso (t : ℕ) (b : FundamentalGroupoid B) :
    (fiberLocalSystem Λ k t).obj b ≅
      ((singularChains k).obj (p.fiber b.as)).homology t :=
  fiberLocalSystemObjIso Λ k t b ≪≫ (singularCubicalHomologyIso k (p.fiber b.as) t).symm

theorem fiberLocalSystemSingularObjIso_hom (t : ℕ) (b : FundamentalGroupoid B) :
    (fiberLocalSystemSingularObjIso Λ k t b).hom =
      (fiberLocalSystemObjIso Λ k t b).hom ≫ (singularCubicalHomologyIso k (p.fiber b.as) t).inv :=
  (rfl)

theorem fiberLocalSystemSingularObjIso_inv (t : ℕ) (b : FundamentalGroupoid B) :
    (fiberLocalSystemSingularObjIso Λ k t b).inv =
      (singularCubicalHomologyIso k (p.fiber b.as) t).hom ≫ (fiberLocalSystemObjIso Λ k t b).inv :=
  (rfl)

/-- Read on simplicial singular homology through `TauCeti.fiberLocalSystemSingularObjIso`, the
fiber local system sends the class of a path to the map induced by the transport along it. -/
theorem fiberLocalSystem_map_mk_singular (t : ℕ) {b₀ b₁ : FundamentalGroupoid B}
    (γ : Path b₀.as b₁.as) :
    (fiberLocalSystem Λ k t).map (Path.Homotopic.Quotient.mk γ) =
      (fiberLocalSystemSingularObjIso Λ k t b₀).hom ≫
        HomologicalComplex.homologyMap ((singularChains k).map (fiberTransport Λ γ)) t ≫
        (fiberLocalSystemSingularObjIso Λ k t b₁).inv := by
  rw [fiberLocalSystem_map_mk Λ k t γ, fiberLocalSystemSingularObjIso_hom,
    fiberLocalSystemSingularObjIso_inv, Category.assoc,
    ← Category.assoc (HomologicalComplex.homologyMap ((singularChains k).map _) t),
    singularCubicalHomologyIso_hom_naturality, Category.assoc, Iso.inv_hom_id_assoc]

/-- Transport in the fiber local system acts on simplicial singular homology classes as
`ContinuousMap.singularHomologyMap` of `Λ.transport γ`. -/
@[simp]
theorem fiberLocalSystemSingularObjIso_hom_map_mk (t : ℕ) {b₀ b₁ : FundamentalGroupoid B}
    (γ : Path b₀.as b₁.as) (x : (fiberLocalSystem Λ k t).obj b₀) :
    (fiberLocalSystemSingularObjIso Λ k t b₁).hom
        ((fiberLocalSystem Λ k t).map (Path.Homotopic.Quotient.mk γ) x) =
      ContinuousMap.singularHomologyMap k t (Λ.transport γ)
        ((fiberLocalSystemSingularObjIso Λ k t b₀).hom x) := by
  have h := congrArg (fun φ ↦ (φ ≫ (fiberLocalSystemSingularObjIso Λ k t b₁).hom) x)
    (fiberLocalSystem_map_mk_singular Λ k t γ)
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id, ModuleCat.comp_apply,
    fiberTransport] using h

end TauCeti

namespace CategoryTheory.CommSq

open TauCeti

variable {E B E' B' : TopCat.{u}} {f : E ⟶ E'} {p : E ⟶ B} {p' : E' ⟶ B'} {g : B ⟶ B'}

/-- **Functoriality of the fiber local system in commutative squares.** A commutative square from
`p` to `p'` maps the fiber local system of `p` to the pullback along `g` of the fiber local system
of `p'`, acting on each fiber by the map induced by `CommSq.fiberMap`. -/
def fiberLocalSystemMap (sq : CommSq f p p' g) (Λ : LiftingFunction p.hom)
    (Λ' : LiftingFunction p'.hom) (k : Type u) [Ring k] (t : ℕ) :
    fiberLocalSystem Λ k t ⟶
      (LocalCoefficientSystem.pullback g.hom).obj (fiberLocalSystem Λ' k t) where
  app b :=
    (fiberLocalSystemObjIso Λ k t b).hom ≫
      HomologicalComplex.homologyMap
        ((normalizedCubicalChainComplex k).map (sq.fiberMap b.as)) t ≫
      (fiberLocalSystemObjIso Λ' k t (.mk (g b.as))).inv
  naturality {b₀ b₁} q := by
    induction q using Path.Homotopic.Quotient.ind with | mk γ =>
    -- The pulled-back functor agrees with `fiberLocalSystem Λ' k t` on `.mk (g b.as)` only up to
    -- unfolding `FundamentalGroupoid.map`, so `change` aligns the endpoints once before `rw`.
    change (fiberLocalSystem Λ k t).map (Path.Homotopic.Quotient.mk γ) ≫
        ((fiberLocalSystemObjIso Λ k t b₁).hom ≫
          HomologicalComplex.homologyMap
            ((normalizedCubicalChainComplex k).map (sq.fiberMap b₁.as)) t ≫
          (fiberLocalSystemObjIso Λ' k t (.mk (g b₁.as))).inv) =
      ((fiberLocalSystemObjIso Λ k t b₀).hom ≫
          HomologicalComplex.homologyMap
            ((normalizedCubicalChainComplex k).map (sq.fiberMap b₀.as)) t ≫
          (fiberLocalSystemObjIso Λ' k t (.mk (g b₀.as))).inv) ≫
        (fiberLocalSystem Λ' k t).map (Path.Homotopic.Quotient.mk (γ.map g.hom.continuous))
    rw [fiberLocalSystem_map_mk Λ k t γ, fiberLocalSystem_map_mk Λ' k t (γ.map g.hom.continuous)]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    congr 1
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    obtain ⟨H⟩ := (Λ'.transport_comp_homotopic Λ (fun x ↦ ConcreteCategory.congr_hom sq.w x) γ
      (g₀ := (sq.fiberMap b₀.as).hom) (g₁ := (sq.fiberMap b₁.as).hom)
      (sq.fiberMap_apply_coe b₀.as) (sq.fiberMap_apply_coe b₁.as)).symm
    exact TopCat.Homotopy.congr_homologyMap_normalizedCubicalChainComplex (k := k)
      (f := fiberTransport Λ γ ≫ sq.fiberMap b₁.as)
      (g := sq.fiberMap b₀.as ≫ fiberTransport Λ' (γ.map g.hom.continuous)) H t

theorem fiberLocalSystemMap_app (sq : CommSq f p p' g) (Λ : LiftingFunction p.hom)
    (Λ' : LiftingFunction p'.hom) (k : Type u) [Ring k] (t : ℕ) (b : FundamentalGroupoid B) :
    (sq.fiberLocalSystemMap Λ Λ' k t).app b =
      (fiberLocalSystemObjIso Λ k t b).hom ≫
        HomologicalComplex.homologyMap
          ((normalizedCubicalChainComplex k).map (sq.fiberMap b.as)) t ≫
        (fiberLocalSystemObjIso Λ' k t (.mk (g b.as))).inv :=
  (rfl)

/-- Through `TauCeti.fiberLocalSystemSingularObjIso`, `CommSq.fiberLocalSystemMap` acts on each
fiber as the map on simplicial singular homology induced by `CommSq.fiberMap`. -/
theorem fiberLocalSystemMap_app_singular (sq : CommSq f p p' g) (Λ : LiftingFunction p.hom)
    (Λ' : LiftingFunction p'.hom) (k : Type u) [Ring k] (t : ℕ) (b : FundamentalGroupoid B) :
    (sq.fiberLocalSystemMap Λ Λ' k t).app b ≫
        (fiberLocalSystemSingularObjIso Λ' k t (.mk (g b.as))).hom =
      (fiberLocalSystemSingularObjIso Λ k t b).hom ≫
        HomologicalComplex.homologyMap ((singularChains k).map (sq.fiberMap b.as)) t := by
  -- As in `naturality`, the codomain of `app b` is `(pullback g.hom).obj ...`, which matches
  -- `(fiberLocalSystem Λ' k t).obj (.mk (g b.as))` by unfolding `FundamentalGroupoid.map`.
  change ((fiberLocalSystemObjIso Λ k t b).hom ≫
        HomologicalComplex.homologyMap
          ((normalizedCubicalChainComplex k).map (sq.fiberMap b.as)) t ≫
        (fiberLocalSystemObjIso Λ' k t (.mk (g b.as))).inv) ≫
      (fiberLocalSystemSingularObjIso Λ' k t (.mk (g b.as))).hom = _
  rw [fiberLocalSystemSingularObjIso_hom, fiberLocalSystemSingularObjIso_hom,
    Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, Category.assoc]
  congr 1
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
  exact (singularCubicalHomologyIso_hom_naturality (sq.fiberMap b.as) t).symm

/-- Elementwise on simplicial singular homology classes, `CommSq.fiberLocalSystemMap` acts by
`ContinuousMap.singularHomologyMap` of `CommSq.fiberMap`. -/
theorem fiberLocalSystemSingularObjIso_hom_fiberLocalSystemMap_app
    (sq : CommSq f p p' g) (Λ : LiftingFunction p.hom) (Λ' : LiftingFunction p'.hom)
    (k : Type u) [Ring k] (t : ℕ) (b : FundamentalGroupoid B)
    (x : (fiberLocalSystem Λ k t).obj b) :
    (fiberLocalSystemSingularObjIso Λ' k t (.mk (g b.as))).hom
        ((sq.fiberLocalSystemMap Λ Λ' k t).app b x) =
      ContinuousMap.singularHomologyMap k t (sq.fiberMap b.as).hom
        ((fiberLocalSystemSingularObjIso Λ k t b).hom x) :=
  ConcreteCategory.congr_hom (sq.fiberLocalSystemMap_app_singular Λ Λ' k t b) x

/-- When a commutative square of fibrations induces isomorphisms on every fiber (for instance, in a
topological pullback square), `CommSq.fiberLocalSystemMap` is an isomorphism of local systems. -/
instance isIso_fiberLocalSystemMap (sq : CommSq f p p' g) (Λ : LiftingFunction p.hom)
    (Λ' : LiftingFunction p'.hom) (k : Type u) [Ring k] (t : ℕ)
    [∀ b, IsIso (sq.fiberMap b)] : IsIso (sq.fiberLocalSystemMap Λ Λ' k t) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro b
  -- Unfold `app b` across the definitional equality `((FundamentalGroupoid.map g.hom).obj b) =
  -- .mk (g b.as)` so each factor's domain and codomain match at reducible transparency.
  change IsIso ((fiberLocalSystemObjIso Λ k t b).hom ≫
    HomologicalComplex.homologyMap
      ((normalizedCubicalChainComplex k).map (sq.fiberMap b.as)) t ≫
    (fiberLocalSystemObjIso Λ' k t (.mk (g b.as))).inv)
  have : IsIso (HomologicalComplex.homologyMap
      ((normalizedCubicalChainComplex k).map (sq.fiberMap b.as)) t) :=
    inferInstanceAs (IsIso
      ((normalizedCubicalChainComplex k ⋙ HomologicalComplex.homologyFunctor _ _ t).map
        (sq.fiberMap b.as)))
  infer_instance

end CategoryTheory.CommSq
