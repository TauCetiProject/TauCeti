/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.LocalCoefficients.Normalized
public import TauCeti.AlgebraicTopology.Singular.Cubical.Normalized

/-!
# Pushing cubical chains of a simply connected space into chains with local coefficients

Let `L` be a local coefficient system on `X` and `f : Z → X` a map from a simply connected space,
with a base point `z₀ : Z`.  A singular cube `d` of `Z` together with a coefficient
`a ∈ L(f z₀)` gives a cube of `X` with a coefficient: the cube `f ∘ d` with `a` transported from
`f z₀` to its origin along the path class inside the image of `f` (`ContinuousMap.pathClass`).
Extended to integral normalized cubical chains of `Z`, this is the **twisted pushforward**
`NormalizedTwistedCubicalChain.pushforward L f z₀`, the cubical counterpart of
`TauCeti.LocalCoefficientSystem.twistedPushforward`.  It commutes with the boundaries, changes
source along maps of simply connected spaces by changing the base point, and is natural in the
space and in the coefficient system.

## Main definitions

* `TauCeti.LocalCoefficientSystem.TwistedCubicalChain.pushCube L f z₀ d`: the cube `f ∘ d` with
  the transported coefficient.
* `TauCeti.LocalCoefficientSystem.NormalizedTwistedCubicalChain.pushforward L f z₀ n`: the
  twisted pushforward of integral normalized cubical `n`-chains of `Z`.

## Main results

* `TauCeti.LocalCoefficientSystem.NormalizedTwistedCubicalChain.boundary_pushforward`: it
  commutes with the boundaries.
* `TauCeti.LocalCoefficientSystem.NormalizedTwistedCubicalChain.pushforward_map`: change of the
  source, with change of base point.
* `TauCeti.LocalCoefficientSystem.NormalizedTwistedCubicalChain.map_pushforward`,
  `TauCeti.LocalCoefficientSystem.NormalizedTwistedCubicalChain.coefficientMap_pushforward`:
  naturality in the space and in the coefficient system.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II.
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter XIV.
-/

public section

noncomputable section

open CategoryTheory unitInterval

universe u v w

namespace TauCeti

namespace LocalCoefficientSystem

open SingularCube
open ContinuousMap (pathClass pathClass_comp_pathClass pathClass_comp)

variable {R : Type u} [Ring R] {X : TopCat.{v}} {Z : Type*} [TopologicalSpace Z]
  [SimplyConnectedSpace Z] (L : LocalCoefficientSystem.{u, v, w} R X) (f : C(Z, X)) (z₀ : Z)

namespace TwistedCubicalChain

/-- The cube `f ∘ d` of `X`, with a coefficient at `f z₀` transported to its origin along the
path class inside the image of `f`. -/
def pushCube {m : ℕ} (d : SingularCube Z m) :
    L.obj (FundamentalGroupoid.mk (f z₀)) →ₗ[R] L.TwistedCubicalChain m :=
  ofCube L (f.comp d) ∘ₗ (L.map (f.pathClass z₀ (d 0))).hom

variable {L f z₀}

/-- The value of `pushCube`. -/
theorem pushCube_apply {m : ℕ} (d : SingularCube Z m) (a : L.obj (FundamentalGroupoid.mk (f z₀))) :
    pushCube L f z₀ d a = ofCube L (f.comp d) (L.map (f.pathClass z₀ (d 0)) a) := by
  rw [pushCube, LinearMap.comp_apply]

/-- A subcube of a pushed cube is the pushed subcube. -/
theorem ofSubcube_pushCube {k m : ℕ} (d : SingularCube Z m) (ι : C(Fin k → I, Fin m → I))
    (a : L.obj (FundamentalGroupoid.mk (f z₀))) :
    ofSubcube L (f.comp d) ι (L.map (f.pathClass z₀ (d 0)) a) = pushCube L f z₀ (d.comp ι) a := by
  rw [ofSubcube_apply, pushCube_apply, ← ModuleCat.comp_apply, ← L.map_comp]
  -- `(f.comp d).comp ι` is `f.comp (d.comp ι)` by definition, and the transport inside the
  -- subcube is a transport inside the image of `f`.
  exact congrArg (fun p ↦ ofCube L (f.comp (d.comp ι)) (L.map p a))
    ((congrArg (f.pathClass z₀ (d 0) ≫ ·) (pathClass_comp f d 0 (ι 0))).trans
      (pathClass_comp_pathClass f _ _ _))

/-- The boundary of a pushed cube is the alternating sum of its pushed faces. -/
theorem boundary_pushCube {m : ℕ} (d : SingularCube Z (m + 1))
    (a : L.obj (FundamentalGroupoid.mk (f z₀))) :
    boundary L m (pushCube L f z₀ d a) =
      ∑ i : Fin (m + 1), ((-1 : ℤ) ^ (i : ℕ)) •
        (pushCube L f z₀ (face i 0 d) a - pushCube L f z₀ (face i 1 d) a) := by
  rw [pushCube_apply, boundary_ofCube]
  simp only [ofSubcube_pushCube, comp_face_id]

/-- A degenerate cube pushes forward to a degenerate chain. -/
theorem pushCube_mem_degenerate {m : ℕ} {d : SingularCube Z m} (hd : IsDegenerate d)
    (a : L.obj (FundamentalGroupoid.mk (f z₀))) : pushCube L f z₀ d a ∈ degenerate L m := by
  rw [pushCube_apply]
  exact ofCube_mem_degenerate (hd.comp f) _

/-- Pushing a cube `g ∘ d` forward along `f` is pushing `d` forward along `f ∘ g` from the base
point `w₀`, after transporting the coefficient from `f z₀` to `f (g w₀)`. -/
theorem pushCube_comp {Z' : Type*} [TopologicalSpace Z'] [SimplyConnectedSpace Z'] (g : C(Z', Z))
    (w₀ : Z') {m : ℕ} (d : SingularCube Z' m) (a : L.obj (FundamentalGroupoid.mk (f z₀))) :
    pushCube L (f.comp g) w₀ d (L.map (f.pathClass z₀ (g w₀)) a) =
      pushCube L f z₀ (g.comp d) a := by
  rw [pushCube_apply, pushCube_apply, ← ModuleCat.comp_apply, ← L.map_comp]
  exact congrArg (fun p ↦ ofCube L (f.comp (g.comp d)) (L.map p a))
    ((congrArg (f.pathClass z₀ (g w₀) ≫ ·) (pathClass_comp f g w₀ (d 0))).trans
      (pathClass_comp_pathClass f _ _ _))

/-- Pushing forward along a map `h : X → Y` after pushing a cube forward with coefficients in the
pulled back system is pushing the cube forward along `h ∘ f`. -/
theorem map_pushCube {Y : TopCat.{v}} (h : C(X, Y)) (L : LocalCoefficientSystem.{u, v, w} R Y)
    {m : ℕ} (d : SingularCube Z m)
    (a : ((pullback h).obj L).obj (FundamentalGroupoid.mk (f z₀))) :
    map h L m (pushCube ((pullback h).obj L) f z₀ d a) = pushCube L (h.comp f) z₀ d a := by
  rw [pushCube_apply, map_ofCube]
  -- The fibres of the pulled back system are the fibres of `L` at the images by definition.
  exact (congrArg (fun p ↦ ofCube L (h.comp (f.comp d)) (L.map p a))
    (ContinuousMap.map_pathClass h f z₀ (d 0))).trans
      (pushCube_apply (L := L) (f := h.comp f) (z₀ := z₀) d a).symm

/-- A morphism of local systems acts on a pushed cube through the transported coefficient. -/
theorem coefficientMap_pushCube {K : LocalCoefficientSystem.{u, v, w} R X} (η : L ⟶ K) {m : ℕ}
    (d : SingularCube Z m) (a : L.obj (FundamentalGroupoid.mk (f z₀))) :
    coefficientMap η m (pushCube L f z₀ d a) = pushCube K f z₀ d (η.app _ a) := by
  rw [pushCube_apply, coefficientMap_ofCube, pushCube_apply, NatTrans.naturality_apply]

end TwistedCubicalChain

namespace NormalizedTwistedCubicalChain

open TwistedCubicalChain

/-- The **twisted pushforward** of integral normalized cubical chains of a simply connected space
`Z` along `f : Z → X`: a cube `d` with a coefficient `a ∈ L(f z₀)` goes to the cube `f ∘ d` with
the coefficient transported from `f z₀` to its origin. -/
def pushforward (n : ℕ) :
    NormalizedCubicalChain Z (ULift.{v} ℤ) n →ₗ[ULift.{v} ℤ]
      (L.obj (FundamentalGroupoid.mk (f z₀)) →ₗ[R] L.NormalizedTwistedCubicalChain n) :=
  Submodule.liftQ _ (Finsupp.linearCombination (ULift.{v} ℤ)
      fun d ↦ (TwistedCubicalChain.degenerate L n).mkQ ∘ₗ pushCube L f z₀ d) fun y hy ↦ by
    rw [LinearMap.mem_ker]
    refine CubicalChain.degenerate_induction (ULift.{v} ℤ)
      (P := fun y ↦ Finsupp.linearCombination (ULift.{v} ℤ)
        (fun d ↦ (TwistedCubicalChain.degenerate L n).mkQ ∘ₗ pushCube L f z₀ d) y = 0)
      (map_zero _) (fun d hd ↦ ?_)
      (fun y y' hy hy' ↦ by rw [map_add, hy, hy', add_zero])
      (fun r y hy ↦ by rw [map_smul, hy, smul_zero]) hy
    ext a
    rw [Finsupp.linearCombination_single, one_smul, LinearMap.comp_apply,
      Submodule.mkQ_apply, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
    exact pushCube_mem_degenerate hd a

variable {L f z₀}

/-- The twisted pushforward of the class of a cube. -/
@[simp]
theorem pushforward_ofCube {n : ℕ} (d : SingularCube Z n)
    (a : L.obj (FundamentalGroupoid.mk (f z₀))) :
    pushforward L f z₀ n (NormalizedCubicalChain.ofCube Z (ULift.{v} ℤ) d) a =
      Submodule.Quotient.mk (pushCube L f z₀ d a) := by
  rw [pushforward, NormalizedCubicalChain.ofCube_def, Submodule.liftQ_apply,
    Finsupp.linearCombination_single, one_smul, LinearMap.comp_apply, Submodule.mkQ_apply]

omit [SimplyConnectedSpace Z] in
/-- **Induction on integral normalized cubical chains.** -/
@[elab_as_elim]
private theorem induction {n : ℕ} {P : NormalizedCubicalChain Z (ULift.{v} ℤ) n → Prop}
    (y : NormalizedCubicalChain Z (ULift.{v} ℤ) n) (zero : P 0)
    (cube : ∀ d, P (NormalizedCubicalChain.ofCube Z (ULift.{v} ℤ) d))
    (add : ∀ y y', P y → P y' → P (y + y')) (smul : ∀ (r : ULift.{v} ℤ) y, P y → P (r • y)) :
    P y := by
  induction y using Submodule.Quotient.induction_on with
  | H y =>
    induction y using Finsupp.induction_linear with
    | zero => exact zero
    | add y y' hy hy' => exact add _ _ hy hy'
    | single d r =>
      rw [← Finsupp.smul_single_one, Submodule.Quotient.mk_smul]
      exact smul r _ (by rw [← NormalizedCubicalChain.ofCube_def]; exact cube d)

/-- The twisted pushforward commutes with the boundaries. -/
theorem boundary_pushforward {n : ℕ} (y : NormalizedCubicalChain Z (ULift.{v} ℤ) (n + 1))
    (a : L.obj (FundamentalGroupoid.mk (f z₀))) :
    boundary L n (pushforward L f z₀ (n + 1) y a) =
      pushforward L f z₀ n (NormalizedCubicalChain.boundary Z (ULift.{v} ℤ) n y) a := by
  induction y using induction with
  | zero => simp
  | cube d =>
    rw [pushforward_ofCube, boundary_mk, boundary_pushCube, NormalizedCubicalChain.boundary_ofCube]
    simp [map_sum, map_sub, ULift.smul_def, pushforward_ofCube, ← Submodule.mkQ_apply]
  | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']
  | smul r y hy => simp only [LinearMap.smul_apply, ULift.smul_def, map_zsmul, hy]

/-- **Change of source.** Pushing forward the image of a chain under a map `g : Z' → Z` of simply
connected spaces is pushing forward the chain along `f ∘ g`, from the base point `w₀` of `Z'`,
after transporting the coefficient from `f z₀` to `f (g w₀)`. -/
theorem pushforward_map {Z' : Type*} [TopologicalSpace Z'] [SimplyConnectedSpace Z']
    (g : C(Z', Z)) (w₀ : Z') {n : ℕ} (y : NormalizedCubicalChain Z' (ULift.{v} ℤ) n)
    (a : L.obj (FundamentalGroupoid.mk (f z₀))) :
    pushforward L f z₀ n (NormalizedCubicalChain.map (ULift.{v} ℤ) g n y) a =
      pushforward L (f.comp g) w₀ n y (L.map (f.pathClass z₀ (g w₀)) a) := by
  induction y using induction with
  | zero => simp
  | cube d => rw [NormalizedCubicalChain.map_ofCube, pushforward_ofCube, pushforward_ofCube,
      pushCube_comp]
  | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']
  | smul r y hy => simp only [LinearMap.smul_apply, ULift.smul_def, map_zsmul, hy]

/-- The twisted pushforward is natural in the space. -/
theorem map_pushforward {Y : TopCat.{v}} (h : C(X, Y)) (L : LocalCoefficientSystem.{u, v, w} R Y)
    {n : ℕ} (y : NormalizedCubicalChain Z (ULift.{v} ℤ) n)
    (a : ((pullback h).obj L).obj (FundamentalGroupoid.mk (f z₀))) :
    map h L n (pushforward ((pullback h).obj L) f z₀ n y a) =
      pushforward L (h.comp f) z₀ n y a := by
  induction y using induction with
  | zero =>
    rw [map_zero, LinearMap.zero_apply, map_zero, map_zero]
    rfl
  | cube d =>
    rw [pushforward_ofCube, map_mk, map_pushCube]
    exact (pushforward_ofCube (L := L) (f := h.comp f) (z₀ := z₀) d a).symm
  -- The fibres of the pulled back system are those of `L` only by definition, which leaves the
  -- evaluation of a sum or a multiple of linear maps to be closed by `rfl`.
  | add y y' hy hy' =>
    simp only [map_add, LinearMap.add_apply, hy, hy']
    rfl
  | smul r y hy =>
    simp only [LinearMap.smul_apply, ULift.smul_def, map_zsmul, hy]
    rfl

/-- The twisted pushforward is natural in the coefficient system. -/
theorem coefficientMap_pushforward {K : LocalCoefficientSystem.{u, v, w} R X} (η : L ⟶ K) {n : ℕ}
    (y : NormalizedCubicalChain Z (ULift.{v} ℤ) n) (a : L.obj (FundamentalGroupoid.mk (f z₀))) :
    coefficientMap η n (pushforward L f z₀ n y a) = pushforward K f z₀ n y (η.app _ a) := by
  induction y using induction with
  | zero => simp
  | cube d =>
    rw [pushforward_ofCube, pushforward_ofCube, coefficientMap_mk, coefficientMap_pushCube]
  | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']
  | smul r y hy => simp only [LinearMap.smul_apply, ULift.smul_def, map_zsmul, hy]

end NormalizedTwistedCubicalChain

end LocalCoefficientSystem

end TauCeti
