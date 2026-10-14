/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.CategoryTheory.Limits.Cones
public import TauCeti.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import TauCeti.AlgebraicTopology.LocalCoefficient
public import TauCeti.AlgebraicTopology.Singular.Cubical.Chains
public import TauCeti.Topology.Homotopy.Cube.Basic
import Mathlib.Data.Fin.Parity

/-!
# Unnormalized cubical chains with local coefficients

Let `L` be a local coefficient system on a space `X`.  The **cubical `n`-chains of `X` with
coefficients in `L`** are the direct sum, over the singular `n`-cubes `c` of `X`, of the fibre of
`L` at the origin `c 0` of the cube.  The boundary of a cube `c` carrying a coefficient `a` is the
alternating sum of its faces,

`∂ (c, a) = Σᵢ (-1) ^ i ((face i 0 c, a) - (face i 1 c, τᵢ a))`,

where `τᵢ` transports `a` from the origin of `c` to the origin of its face `face i 1 c` along the
image under `c` of a path in the cube.  The cube is simply connected, so the path class it
transports along is determined by its endpoints (`ContinuousMap.pathClass`); this is what
makes the boundary square to zero, exactly as for constant coefficients.  This is the cubical
version of the singular chains with local coefficients of
`TauCeti.AlgebraicTopology.Singular.Twisted.Basic`, and the complex on which Serre's spectral
sequence of a fibre space is built.

Chains are functorial in the coefficient system (`coefficientMap`) and in the space: a continuous
map `f : X → Y` sends the chains of `X` with coefficients in the pulled back system `f⁎L` to the
chains of `Y` with coefficients in `L` (`map`).  In degree zero, a cocone `s` over `L`, for
instance the colimit of `L` or the module `M` of a constant system, gives an augmentation
`C^□_0(X; L) → s.pt` which vanishes on boundaries.

## Main definitions

* `TauCeti.LocalCoefficientSystem.TwistedCubicalChain L n`: the cubical `n`-chains with
  coefficients in `L`, with `ofCube L c`, the inclusion of the summand of a cube.
* `TauCeti.LocalCoefficientSystem.TwistedCubicalChain.boundary L n`: the boundary.
* `TauCeti.LocalCoefficientSystem.TwistedCubicalChain.coefficientMap η n`,
  `TauCeti.LocalCoefficientSystem.TwistedCubicalChain.map f L n`: functoriality in the
  coefficient system and in the space.
* `TauCeti.LocalCoefficientSystem.TwistedCubicalChain.augment s`: the augmentation into a cocone.

## Main results

* `TauCeti.LocalCoefficientSystem.TwistedCubicalChain.boundary_boundary`: `∂ ∘ ∂ = 0`.
* `TauCeti.LocalCoefficientSystem.TwistedCubicalChain.map_boundary`,
  `TauCeti.LocalCoefficientSystem.TwistedCubicalChain.coefficientMap_boundary`: the boundary is
  natural.
* `TauCeti.LocalCoefficientSystem.TwistedCubicalChain.map_id`,
  `TauCeti.LocalCoefficientSystem.TwistedCubicalChain.map_comp`,
  `TauCeti.LocalCoefficientSystem.TwistedCubicalChain.coefficientMap_map`: functoriality.
* `TauCeti.LocalCoefficientSystem.TwistedCubicalChain.augment_boundary`: `ε ∘ ∂ = 0`.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II.
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapters II and XIV.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §7.2.
-/

public section

noncomputable section

open CategoryTheory Limits unitInterval

universe u v w

namespace TauCeti

namespace LocalCoefficientSystem

open SingularCube
open ContinuousMap (pathClass pathClass_self pathClass_comp_pathClass pathClass_comp map_pathClass)

variable {R : Type u} [Ring R] {X Y Z : TopCat.{v}}

/-- The **cubical `n`-chains with coefficients in a local system** `L`: the direct sum, over the
singular `n`-cubes `c`, of the fibre of `L` at the origin of `c`. -/
abbrev TwistedCubicalChain (L : LocalCoefficientSystem.{u, v, w} R X) (n : ℕ) : Type (max v w) :=
  DirectSum (SingularCube X n) fun c ↦ L.obj (FundamentalGroupoid.mk (c 0))

namespace TwistedCubicalChain

section Basic

variable (L : LocalCoefficientSystem.{u, v, w} R X)

open scoped Classical in
/-- The inclusion of the summand of a singular cube into the cubical chains. -/
def ofCube {n : ℕ} (c : SingularCube X n) :
    L.obj (FundamentalGroupoid.mk (c 0)) →ₗ[R] L.TwistedCubicalChain n :=
  DirectSum.lof R _ (fun c : SingularCube X n ↦ L.obj (FundamentalGroupoid.mk (c 0))) c

open scoped Classical in
/-- The linear map out of the cubical chains with prescribed values on each summand. -/
def desc {n : ℕ} {N : Type*} [AddCommGroup N] [Module R N]
    (φ : ∀ c : SingularCube X n, L.obj (FundamentalGroupoid.mk (c 0)) →ₗ[R] N) :
    L.TwistedCubicalChain n →ₗ[R] N :=
  DirectSum.toModule R _ N φ

variable {L}

open scoped Classical in
/-- The map with prescribed values on summands restricts to the prescribed map on each summand. -/
@[simp]
theorem desc_ofCube {n : ℕ} {N : Type*} [AddCommGroup N] [Module R N]
    (φ : ∀ c : SingularCube X n, L.obj (FundamentalGroupoid.mk (c 0)) →ₗ[R] N)
    (c : SingularCube X n) (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    desc L φ (ofCube L c a) = φ c a := by
  rw [desc, ofCube]
  exact DirectSum.toModule_lof
    (M := fun c : SingularCube X n ↦ L.obj (FundamentalGroupoid.mk (c 0))) R c a

open scoped Classical in
/-- Two linear maps out of the cubical chains agree as soon as they agree on every summand. -/
@[ext]
theorem hom_ext {n : ℕ} {N : Type*} [AddCommGroup N] [Module R N]
    {f g : L.TwistedCubicalChain n →ₗ[R] N} (h : ∀ c, f ∘ₗ ofCube L c = g ∘ₗ ofCube L c) :
    f = g := by
  refine DirectSum.linearMap_ext R fun c ↦ ?_
  have hc := h c
  rwa [ofCube] at hc

open scoped Classical in
/-- **Induction on cubical chains**: a property of chains which holds for `0`, for each cube with
a coefficient, and is stable under sums, holds for every chain. -/
@[elab_as_elim]
theorem induction_on {n : ℕ} {P : L.TwistedCubicalChain n → Prop} (x : L.TwistedCubicalChain n)
    (zero : P 0)
    (ofCube : ∀ c a, P (ofCube L c a)) (add : ∀ x y, P x → P y → P (x + y)) : P x := by
  refine DirectSum.induction_on x zero (fun c a ↦ ?_) add
  have hc := ofCube c a
  rwa [TwistedCubicalChain.ofCube] at hc

variable (L) in
/-- The summand of the subcube `c ∘ ι` of a cube `c`, with the coefficient transported from the
origin of `c` to the origin of the subcube along the path class inside `c`. -/
def ofSubcube {m n : ℕ} (c : SingularCube X n) (ι : C(Fin m → I, Fin n → I)) :
    L.obj (FundamentalGroupoid.mk (c 0)) →ₗ[R] L.TwistedCubicalChain m :=
  ofCube L (c.comp ι) ∘ₗ (L.map (pathClass c 0 (ι 0))).hom

/-- A subcube with a coefficient is the summand of the subcube with the transported coefficient. -/
theorem ofSubcube_apply {m n : ℕ} (c : SingularCube X n) (ι : C(Fin m → I, Fin n → I))
    (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    ofSubcube L c ι a = ofCube L (c.comp ι) (L.map (pathClass c 0 (ι 0)) a) := by
  rw [ofSubcube, LinearMap.comp_apply]

/-- The cube itself is the subcube along the identity. -/
@[simp]
theorem ofSubcube_id {n : ℕ} (c : SingularCube X n) :
    ofSubcube L c (ContinuousMap.id _) = ofCube L c := by
  refine LinearMap.ext fun a ↦ ?_
  rw [ofSubcube_apply]
  change ofCube L c (L.map (pathClass c 0 0) a) = _
  rw [pathClass_self, CategoryTheory.Functor.map_id]
  rfl

/-- A subcube of a subcube is a subcube. -/
theorem ofSubcube_comp {k m n : ℕ} (c : SingularCube X n) (ι : C(Fin m → I, Fin n → I))
    (κ : C(Fin k → I, Fin m → I)) (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    ofSubcube L (c.comp ι) κ (L.map (pathClass c 0 (ι 0)) a) = ofSubcube L c (ι.comp κ) a := by
  rw [ofSubcube_apply, ofSubcube_apply, pathClass_comp, ← ModuleCat.comp_apply, ← L.map_comp,
    pathClass_comp_pathClass]
  rfl

end Basic

section Boundary

variable (L : LocalCoefficientSystem.{u, v, w} R X)

/-- The boundary of a single `(n+1)`-cube with a coefficient:
`∂ (c, a) = Σᵢ (-1) ^ i ((face i 0 c, τ a) - (face i 1 c, τ' a))`, the coefficient being
transported to the origins of the faces. -/
def boundaryCube {n : ℕ} (c : SingularCube X (n + 1)) :
    L.obj (FundamentalGroupoid.mk (c 0)) →ₗ[R] L.TwistedCubicalChain n :=
  ∑ i : Fin (n + 1), ((-1 : ℤ) ^ (i : ℕ)) •
    (ofSubcube L c (face i 0 (ContinuousMap.id _)) - ofSubcube L c (face i 1 (ContinuousMap.id _)))

/-- The **boundary** of cubical chains with local coefficients. -/
def boundary (n : ℕ) : L.TwistedCubicalChain (n + 1) →ₗ[R] L.TwistedCubicalChain n :=
  desc L (boundaryCube L)

variable {L}

/-- The boundary of a cube is the alternating sum of its faces, the subcubes
`c ∘ face i t id`, with the coefficient transported along the path classes inside the cube to the
origins of the faces. -/
@[simp]
theorem boundary_ofCube {n : ℕ} (c : SingularCube X (n + 1))
    (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    boundary L n (ofCube L c a) =
      ∑ i : Fin (n + 1), ((-1 : ℤ) ^ (i : ℕ)) •
        (ofSubcube L c (face i 0 (ContinuousMap.id _)) a -
          ofSubcube L c (face i 1 (ContinuousMap.id _)) a) := by
  rw [boundary, desc_ofCube, boundaryCube]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sub_apply]

private theorem boundary_ofSubcube {m n : ℕ} (c : SingularCube X n)
    (ι : C(Fin (m + 1) → I, Fin n → I)) (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    boundary L m (ofSubcube L c ι a) =
      ∑ j : Fin (m + 1), ((-1 : ℤ) ^ (j : ℕ)) •
        (ofSubcube L c (ι.comp (face j 0 (ContinuousMap.id _))) a -
          ofSubcube L c (ι.comp (face j 1 (ContinuousMap.id _))) a) := by
  rw [ofSubcube_apply, boundary, desc_ofCube, boundaryCube]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sub_apply, ofSubcube_comp]

/-- The boundary of a boundary vanishes. -/
theorem boundary_boundary (n : ℕ) : boundary L n ∘ₗ boundary L (n + 1) = 0 := by
  -- As for `TauCeti.CubicalChain.boundary_boundary`: the terms of `∂ ∂ (c, a)` are subcubes of
  -- `c`, and they cancel in pairs under `faceSwap`, by the cubical identity for the face
  -- inclusions.
  refine hom_ext fun c ↦ LinearMap.ext fun a ↦ ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.zero_apply, ← ofSubcube_id,
    boundary_ofSubcube, map_sum, map_zsmul, map_sub, ← Finset.sum_sub_distrib, Finset.smul_sum]
  rw [← Finset.sum_product']
  refine Finset.sum_involution (fun p _ ↦ (p.1.succAbove p.2, p.2.predAbove p.1)) (fun p _ ↦ ?_)
    (fun p _ _ h ↦ Fin.succAbove_ne p.1 p.2 (congrArg Prod.fst h))
    (fun _ _ ↦ Finset.mem_univ _) (fun p _ ↦ ?_)
  swap
  · simp [Fin.succAbove_succAbove_predAbove, Fin.predAbove_predAbove_succAbove]
  obtain ⟨i, j⟩ := p
  simp only [ContinuousMap.id_comp,
    ← face_id_comp_face_id, smul_sub, smul_smul, ← pow_add,
    Fin.neg_one_pow_succAbove_add_predAbove, neg_smul]
  abel

end Boundary

section CoefficientMap

variable {L K J : LocalCoefficientSystem.{u, v, w} R X}

/-- The map of cubical chains induced by a morphism of local coefficient systems. -/
def coefficientMap (η : L ⟶ K) (n : ℕ) :
    L.TwistedCubicalChain n →ₗ[R] K.TwistedCubicalChain n :=
  desc L fun c ↦ ofCube K c ∘ₗ (η.app (FundamentalGroupoid.mk (c 0))).hom

/-- A morphism of local systems acts on the summand of each cube by its component at the origin. -/
@[simp]
theorem coefficientMap_ofCube (η : L ⟶ K) {n : ℕ} (c : SingularCube X n)
    (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    coefficientMap η n (ofCube L c a) = ofCube K c (η.app _ a) :=
  desc_ofCube _ c a

/-- The identity of a local system induces the identity on cubical chains. -/
@[simp]
theorem coefficientMap_id (n : ℕ) : coefficientMap (𝟙 L) n = LinearMap.id :=
  hom_ext fun c ↦ LinearMap.ext fun a ↦ by simp

/-- A composite of morphisms of local systems induces the composite map on cubical chains. -/
theorem coefficientMap_comp (η : L ⟶ K) (θ : K ⟶ J) (n : ℕ) :
    coefficientMap (η ≫ θ) n = coefficientMap θ n ∘ₗ coefficientMap η n :=
  hom_ext fun c ↦ LinearMap.ext fun a ↦ by simp

/-- A morphism of local systems sends a subcube with a coefficient to the same subcube with the
image coefficient. -/
@[simp]
theorem coefficientMap_ofSubcube (η : L ⟶ K) {m n : ℕ} (c : SingularCube X n)
    (ι : C(Fin m → I, Fin n → I)) (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    coefficientMap η m (ofSubcube L c ι a) = ofSubcube K c ι (η.app _ a) := by
  rw [ofSubcube_apply, ofSubcube_apply, coefficientMap_ofCube, NatTrans.naturality_apply]

/-- The boundary commutes with the maps induced by a morphism of local systems. -/
theorem coefficientMap_boundary (η : L ⟶ K) (n : ℕ) :
    coefficientMap η n ∘ₗ boundary L n = boundary K n ∘ₗ coefficientMap η (n + 1) :=
  hom_ext fun c ↦ LinearMap.ext fun a ↦ by simp

end CoefficientMap

section Map

variable (f : C(X, Y)) (L : LocalCoefficientSystem.{u, v, w} R Y)

/-- The map of cubical chains induced by a continuous map `f`, from the chains with coefficients
in the pulled back system `f⁎L` to the chains with coefficients in `L`. -/
-- The summand of a cube `c` in the source, `L.obj ⟨f (c 0)⟩`, is definitionally the summand of
-- the cube `f.comp c` in the target.
def map (n : ℕ) : ((pullback f).obj L).TwistedCubicalChain n →ₗ[R] L.TwistedCubicalChain n :=
  desc _ fun c ↦ ofCube L (f.comp c)

variable {f L}

/-- A continuous map sends the summand of a cube identically onto the summand of the image cube. -/
theorem map_ofCube {n : ℕ} (c : SingularCube X n)
    (a : ((pullback f).obj L).obj (FundamentalGroupoid.mk (c 0))) :
    map f L n (ofCube _ c a) = ofCube L (f.comp c) a :=
  desc_ofCube _ c a

/-- A continuous map sends a subcube with a coefficient to the image subcube. -/
theorem map_ofSubcube {m n : ℕ} (c : SingularCube X n) (ι : C(Fin m → I, Fin n → I))
    (a : ((pullback f).obj L).obj (FundamentalGroupoid.mk (c 0))) :
    map f L m (ofSubcube _ c ι a) = ofSubcube L (f.comp c) ι a := by
  rw [ofSubcube_apply (L := L) (f.comp c) ι a, ofSubcube_apply, map_ofCube]
  exact congrArg (fun p ↦ ofCube L (f.comp (c.comp ι)) (L.map p a)) (map_pathClass f c 0 (ι 0))

variable (f L) in
/-- The boundary is natural. -/
theorem map_boundary (n : ℕ) :
    map f L n ∘ₗ boundary ((pullback f).obj L) n = boundary L n ∘ₗ map f L (n + 1) :=
  hom_ext fun c ↦ LinearMap.ext fun a ↦ by
    simp only [LinearMap.comp_apply, map_ofCube, boundary_ofCube, map_sum, map_zsmul, map_sub,
      map_ofSubcube]
    rw [boundary_ofCube (L := L) (f.comp c) a]

/-- The map induced by a continuous map is natural in the coefficient system. -/
theorem coefficientMap_map {K : LocalCoefficientSystem.{u, v, w} R Y} (η : L ⟶ K) (n : ℕ) :
    coefficientMap η n ∘ₗ map f L n = map f K n ∘ₗ coefficientMap ((pullback f).map η) n :=
  hom_ext fun c ↦ LinearMap.ext fun a ↦ by
    simp only [LinearMap.comp_apply, map_ofCube, coefficientMap_ofCube]
    exact coefficientMap_ofCube η (f.comp c) a

end Map

section MapComp

/-- The identity map induces on cubical chains the map coming from the identification of a
system with its pullback along the identity. -/
@[simp]
theorem map_id (L : LocalCoefficientSystem.{u, v, w} R X) (n : ℕ) :
    map (ContinuousMap.id X) L n = coefficientMap ((pullbackIdIso X).hom.app L) n :=
  hom_ext fun c ↦ LinearMap.ext fun a ↦ by
    simp only [LinearMap.coe_comp, Function.comp_apply, map_ofCube, coefficientMap_ofCube,
      pullbackIdIso_hom_app_app]
    rfl

/-- A composite of continuous maps induces on cubical chains the composite of the two induced
maps, after the identification of the pullback along the composite with the iterated
pullback. -/
theorem map_comp (f : C(X, Y)) (g : C(Y, Z)) (L : LocalCoefficientSystem.{u, v, w} R Z)
    (n : ℕ) :
    map (g.comp f) L n = map g L n ∘ₗ map f ((pullback g).obj L) n ∘ₗ
      coefficientMap ((pullbackCompIso f g).hom.app L) n :=
  hom_ext fun c ↦ LinearMap.ext fun a ↦ by
    simp only [LinearMap.comp_apply, coefficientMap_ofCube, pullbackCompIso_hom_app_app,
      map_ofCube]
    exact ((congrArg (map g L n) (map_ofCube (L := (pullback g).obj L) (f := f) c _)).trans
      (map_ofCube (f := g) (f.comp c) _)).symm

end MapComp

section Augment

variable {L : LocalCoefficientSystem.{u, v, w} R X}

/-- The **augmentation** of the cubical `0`-chains into a cocone `s` over the local system: a
point `x` with a coefficient `a` goes to the image of `a` under the leg of `s` at `x`.  For the
colimit cocone it takes values in `colimit L`, the zeroth homology with coefficients in `L`; for a
constant system with fibre `M` and the cocone of identities it is the sum of the coefficients. -/
def augment (s : Cocone L) : L.TwistedCubicalChain 0 →ₗ[R] s.pt :=
  desc L fun c ↦ (s.ι.app (FundamentalGroupoid.mk (c 0))).hom

@[simp]
theorem augment_ofCube (s : Cocone L) (c : SingularCube X 0)
    (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    augment s (ofCube L c a) = s.ι.app _ a :=
  desc_ofCube _ c a

/-- The augmentation of a point of a subcube, a vertex of the cube, is the image of the
coefficient at the origin of the cube. -/
@[simp]
theorem augment_ofSubcube (s : Cocone L) {n : ℕ} (c : SingularCube X n)
    (ι : C(Fin 0 → I, Fin n → I)) (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    augment s (ofSubcube L c ι a) = s.ι.app _ a := by
  rw [ofSubcube_apply, augment_ofCube]
  exact ConcreteCategory.congr_hom (s.w (pathClass c 0 (ι 0))) a

/-- The augmentation vanishes on boundaries: a path with a coefficient contributes the images
of the coefficient at both of its end points, which agree in the cocone. -/
theorem augment_boundary (s : Cocone L) : augment s ∘ₗ boundary L 0 = 0 :=
  hom_ext fun c ↦ LinearMap.ext fun a ↦ by simp

/-- The augmentation is natural in the coefficient system. -/
theorem augment_coefficientMap {K : LocalCoefficientSystem.{u, v, w} R X} (η : L ⟶ K)
    (s : Cocone K) :
    augment s ∘ₗ coefficientMap η 0 = augment ((Cocone.precompose η).obj s) :=
  hom_ext fun c ↦ LinearMap.ext fun a ↦ by simp

/-- The augmentation is natural in the space. -/
theorem augment_map (f : C(X, Y)) {L : LocalCoefficientSystem.{u, v, w} R Y} (s : Cocone L) :
    augment s ∘ₗ map f L 0 = augment (s.whisker (FundamentalGroupoid.map f)) :=
  hom_ext fun c ↦ LinearMap.ext fun a ↦ (congrArg (augment s) (map_ofCube c a)).trans
    ((augment_ofCube (L := L) s (f.comp c) a).trans
      (augment_ofCube (s.whisker (FundamentalGroupoid.map f)) c a).symm)

end Augment

end TwistedCubicalChain

end LocalCoefficientSystem

end TauCeti
