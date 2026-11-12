/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.QuasiIso
public import TauCeti.AlgebraicTopology.Singular.Cubical.Compression.Retraction
public import TauCeti.AlgebraicTopology.Singular.Cubical.LocalCoefficients.ChainComplex
public import TauCeti.AlgebraicTopology.Singular.Cubical.LocalCoefficients.Comparison.Homotopy

/-!
# Compression of cubical chains with local coefficients

Let `D` be a `TauCeti.SubspaceCubeDeformation A n`: a deformation of the singular cubes of `X`,
ending in a subspace `A` for the cubes of dimension less than `n`, compatible with faces and
degeneracies and fixing the cubes of `A`. Let `L` be a local coefficient system on `X`. For
`n = ⊤`, this file shows that **the inclusion of `A` induces a chain homotopy equivalence from the
normalized cubical chains of `A` with coefficients in the restriction of `L` to the normalized
cubical chains of `X` with coefficients in `L`**. This is the local-coefficient form of
`TauCeti.SubspaceCubeDeformation.normalizedCubicalChainComplexHomotopyEquiv`. For finite `n`, the
inclusion of `A` is **surjective on homology with coefficients in `L` below degree `n`, and
bijective one degree lower**.

A coefficient of a cube lives in the fibre of `L` at the origin of the cube, so the operators of the
constant case have to move it.

* During the deformation, the origin of a cube `c` of dimension less than `n` traces a path from
  `c 0` to the origin of the end `D.retract hm c` of the deformation. Its class is
  `D.originTransport hm c`. The retraction `D.twistedRetractChain L hm` sends `c` with a
  coefficient `a` to `D.retract hm c` with `a` transported along this path. It commutes with the
  boundary, and it is a left inverse of the inclusion.
* The swept cube `D.sweep c` starts at the origin of `c`, so the swept-cube operator
  `D.twistedPrismChain L` keeps the coefficient. Every transport that occurs in the faces of the
  swept cube, in the retraction and in the faces of `c` is a path class inside the swept cube.
  The cube is simply connected, so such a path class is determined by its end points. Hence the
  prism identity `∂ P + P ∂ = ι ρ - id` holds exactly as for constant coefficients.

For `n = ⊤` these operators are a chain map and a chain homotopy. For finite `n` the swept-cube
operator is still defined in every degree, but the retraction is defined only in degrees below
`n`, and the prism identity holds only in degrees `m` with `m < n`. This is enough to compare the
homology of `A` and `X` there: a cycle `y` of `X` of degree `m < n` is the image of the cycle
`ρ y` up to the boundary of `-P y`, and a cycle `x` of `A` of degree `m` with `m + 1 < n` whose
image bounds `b` in `X` bounds `ρ b` in `A`.

By the compression lemma such a deformation exists as soon as every point of `X` is joined by a
path to `A` and all relative homotopy sets `π_{n+1}(X, A, a)` vanish
(`TauCeti.quasiIso_normalizedTwistedCubicalChainComplexMap_subtypeVal_of_relHomotopyGroup`). For
the inclusion of the bottom face of the mapping cylinder of a weak homotopy equivalence, this is
the main step in the proof that weak homotopy equivalences induce isomorphisms on homology with
local coefficients.

## Main definitions

* `TauCeti.SubspaceCubeDeformation.originTransport`: the class of the path traced by the origin of
  a cube during its deformation.
* `TauCeti.SubspaceCubeDeformation.twistedRetractChain`,
  `TauCeti.SubspaceCubeDeformation.twistedPrismChain`: the retraction and the swept-cube operator
  on normalized cubical chains with local coefficients.
* `TauCeti.SubspaceCubeDeformation.twistedRetractChainMap`,
  `TauCeti.SubspaceCubeDeformation.twistedRetractHomotopy`: the retraction as a chain map, and the
  chain homotopy from the identity to its composite with the inclusion.
* `TauCeti.SubspaceCubeDeformation.normalizedTwistedCubicalChainComplexHomotopyEquiv`: the chain
  homotopy equivalence induced by the inclusion of `A`.

## Main results

* `TauCeti.SubspaceCubeDeformation.twistedRetractChain_map_subtypeVal`: the retraction is a left
  inverse of the inclusion.
* `TauCeti.SubspaceCubeDeformation.boundary_twistedRetractChain`: the retraction commutes with the
  boundary.
* `TauCeti.SubspaceCubeDeformation.boundary_twistedPrismChain_add_twistedPrismChain_boundary`: the
  prism identity `∂ P + P ∂ = ι ρ - id`.
* `TauCeti.SubspaceCubeDeformation.quasiIso_normalizedTwistedCubicalChainComplexMap`: the inclusion
  of `A` induces a quasi-isomorphism of normalized cubical chains with local coefficients.
* `TauCeti.quasiIso_normalizedTwistedCubicalChainComplexMap_subtypeVal_of_relHomotopyGroup`: the
  same conclusion from the vanishing of the relative homotopy sets.
* `TauCeti.SubspaceCubeDeformation.epi_homologyMap_normalizedTwistedCubicalChainComplexMap`,
  `TauCeti.SubspaceCubeDeformation.quasiIsoAt_normalizedTwistedCubicalChainComplexMap`: below the
  dimension bound `n` of the deformation, the inclusion of `A` is surjective on homology with
  local coefficients, and bijective one degree lower.
* `TauCeti.epi_twistedHomologyMap_subtypeVal_of_relHomotopyGroup`,
  `TauCeti.isIso_twistedHomologyMap_subtypeVal_of_relHomotopyGroup_of_add_one_lt`: transported to
  simplicial chains, the inclusion of a subspace is surjective on singular homology with local
  coefficients below the connectivity of the pair, and bijective one degree lower.

## References

* The chain-level construction extends the constant-coefficient one of
  `TauCeti.AlgebraicTopology.Singular.Cubical.Compression.Retraction`.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.H (homology with local coefficients) and Section 4.1, Proposition 4.21 (a weak
  homotopy equivalence induces isomorphisms on homology).
* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II, for cubical chains with local coefficients.
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter II, for normalized
  cubical chains and their prism operators.
-/

public section

noncomputable section

open CategoryTheory unitInterval Set

universe u v w

namespace TauCeti

open SingularCube LocalCoefficientSystem
open ContinuousMap (pathClass pathClass_heq pathClass_comp fromPath_heq_pathClass
  comp_heq_pathClass)

namespace SubspaceCubeDeformation

section Transport

variable {X : Type*} [TopologicalSpace X] {A : Set X} {n : ℕ∞} (D : SubspaceCubeDeformation A n)

/-- The **transport along the track of the origin** of a singular cube `c` of dimension less than
`n`: the class of the path traced by the origin of `c` during its deformation into `A`. -/
def originTransport {m : ℕ} (hm : (m : ℕ∞) < n) (c : SingularCube X m) :
    FundamentalGroupoid.mk (c 0) ⟶ FundamentalGroupoid.mk ((D.retract hm c 0 : A) : X) :=
  FundamentalGroupoid.fromPath
    (Path.Homotopic.Quotient.mk (((D.cubeHomotopy c).evalAt 0).cast rfl (by simp)))

/-- The edge of the cube `I^(m+1)` along the first coordinate. -/
private def firstEdge (m : ℕ) : Path (0 : Fin (m + 1) → I) (Fin.cons 1 0) where
  toFun t := Fin.cons t 0
  continuous_toFun := by fun_prop
  source' := by
    ext i
    cases i using Fin.cases <;> rfl
  target' := rfl

/-- The transport along the track of the origin of `c` is the path class inside the swept cube of
`c` from its origin to the origin of the end of the deformation. -/
theorem originTransport_heq {m : ℕ} (hm : (m : ℕ∞) < n) (c : SingularCube X m) :
    D.originTransport hm c ≍ (D.sweep c).pathClass 0 (Fin.cons 1 0) :=
  fromPath_heq_pathClass (D.sweep c) (firstEdge m) _ fun t ↦ by
    simp [firstEdge, sweep_apply]

/-- The origin of `c` as an object of the fundamental groupoid is the origin of its swept cube. -/
private theorem mk_sweep_zero {m : ℕ} (c : SingularCube X m) :
    FundamentalGroupoid.mk (c 0) = FundamentalGroupoid.mk (D.sweep c 0) :=
  congrArg _ (D.sweep_apply_zero c).symm

private theorem eq_sweep_comp {m : ℕ} (c : SingularCube X m) :
    c = (D.sweep c).comp ⟨fun y ↦ Fin.cons 0 y, by fun_prop⟩ := by
  ext y
  simp [sweep_apply]

private theorem subtypeVal_comp_retract_eq {m : ℕ} (hm : (m : ℕ∞) < n) (c : SingularCube X m) :
    (ContinuousMap.subtypeVal A).comp (D.retract hm c) =
      (D.sweep c).comp ⟨fun y ↦ Fin.cons 1 y, by fun_prop⟩ := by
  ext y
  simp [sweep_apply]

private theorem sweep_comp_face_eq {m : ℕ} (c : SingularCube X (m + 1)) (i : Fin (m + 1)) {t : I}
    (ht : t = 0 ∨ t = 1) :
    D.sweep (c.comp (face i t (ContinuousMap.id _))) =
      (D.sweep c).comp ⟨fun y ↦ i.succ.insertNth t y, by fun_prop⟩ := by
  ext y
  rw [comp_face_id, ← D.face_succ_sweep c i ht, face_apply]
  rfl

/-- Path classes inside `c` are path classes inside the bottom face of its swept cube. -/
private theorem pathClass_heq_sweep {m : ℕ} (c : SingularCube X m) (y z : Fin m → I) :
    c.pathClass y z ≍ (D.sweep c).pathClass (Fin.cons 0 y) (Fin.cons 0 z) :=
  (pathClass_heq (D.eq_sweep_comp c) rfl rfl).trans (heq_of_eq (pathClass_comp _ _ _ _))

/-- Path classes inside the end of the deformation of `c` are path classes inside the top face
of its swept cube. -/
private theorem pathClass_heq_sweep_retract {m : ℕ} (hm : (m : ℕ∞) < n) (c : SingularCube X m)
    (y z : Fin m → I) :
    ((ContinuousMap.subtypeVal A).comp (D.retract hm c)).pathClass y z ≍
      (D.sweep c).pathClass (Fin.cons 1 y) (Fin.cons 1 z) :=
  (pathClass_heq (D.subtypeVal_comp_retract_eq hm c) rfl rfl).trans
    (heq_of_eq (pathClass_comp _ _ _ _))

private theorem face_id_apply_zero {m : ℕ} (i : Fin (m + 1)) (t : I) :
    face i t (ContinuousMap.id (Fin (m + 1) → I)) 0 = i.insertNth t 0 := by
  rw [face_apply, ContinuousMap.id_apply]

private theorem insertNth_succ_zero {m : ℕ} (i : Fin (m + 1)) (t : I) :
    (i.succ.insertNth t 0 : Fin (m + 2) → I) = Fin.cons 0 (i.insertNth t 0) := by
  rw [← Matrix.cons_zero_zero]
  exact Fin.insertNth_succ_cons i t 0 0

/-- Transport into the bottom face of the swept cube is trivial. -/
private theorem eqToHom_comp_pathClass_face_zero_zero_heq {m : ℕ} (c : SingularCube X m) :
    eqToHom (D.mk_sweep_zero c) ≫ (D.sweep c).pathClass 0 (face 0 0 (ContinuousMap.id _) 0) ≍
      𝟙 (FundamentalGroupoid.mk (c 0)) := by
  refine (eqToHom_comp_heq _ _).trans ((pathClass_heq (y' := 0) rfl rfl ?_).trans ?_)
  · rw [face_id_apply_zero, Fin.insertNth_zero']
    exact Matrix.cons_zero_zero
  · rw [ContinuousMap.pathClass_self]
    exact (eqToHom_heq_id_cod _ _ (D.mk_sweep_zero c)).symm.trans
      (eqToHom_heq_id_dom _ _ (D.mk_sweep_zero c))

/-- Transport into the top face of the swept cube is transport along the track of the
origin. -/
private theorem eqToHom_comp_pathClass_face_zero_one_heq {m : ℕ} (hm : (m : ℕ∞) < n)
    (c : SingularCube X m) :
    eqToHom (D.mk_sweep_zero c) ≫ (D.sweep c).pathClass 0 (face 0 1 (ContinuousMap.id _) 0) ≍
      D.originTransport hm c := by
  refine (eqToHom_comp_heq _ _).trans
    ((pathClass_heq rfl rfl ?_).trans (D.originTransport_heq hm c).symm)
  rw [face_id_apply_zero, Fin.insertNth_zero']

/-- Transport into a spatial face of the swept cube is transport inside `c` into the
corresponding face of `c`, followed by the identification with the origin of its swept cube. -/
private theorem eqToHom_comp_pathClass_face_succ_heq {m : ℕ} (c : SingularCube X (m + 1))
    (i : Fin (m + 1)) (t : I) :
    eqToHom (D.mk_sweep_zero c) ≫
        (D.sweep c).pathClass 0 (face i.succ t (ContinuousMap.id _) 0) ≍
      c.pathClass 0 (face i t (ContinuousMap.id _) 0) ≫
        eqToHom (D.mk_sweep_zero (c.comp (face i t (ContinuousMap.id _)))) := by
  refine (eqToHom_comp_heq _ _).trans (HEq.symm ((comp_eqToHom_heq _ _).trans
    ((D.pathClass_heq_sweep c _ _).trans (pathClass_heq rfl (Matrix.cons_zero_zero) ?_))))
  rw [face_id_apply_zero, face_id_apply_zero, insertNth_succ_zero]

/-- Transport along the track of the origin of `c`, followed by transport inside the end of the
deformation into one of its faces, is transport inside `c` into that face followed by
transport along the track of the origin of the face. -/
theorem originTransport_comp_pathClass_heq {m : ℕ} (hm : ((m + 1 : ℕ) : ℕ∞) < n)
    (c : SingularCube X (m + 1)) (i : Fin (m + 1)) {t : I} (ht : t = 0 ∨ t = 1) :
    D.originTransport hm c ≫
        ((ContinuousMap.subtypeVal A).comp (D.retract hm c)).pathClass 0
          (face i t (ContinuousMap.id _) 0) ≍
      c.pathClass 0 (face i t (ContinuousMap.id _) 0) ≫
        D.originTransport ((Nat.cast_le.2 m.le_succ).trans_lt hm)
          (c.comp (face i t (ContinuousMap.id _))) := by
  -- Both sides are the path class inside the swept cube from `0` to `(1, v)`, for the vertex `v`
  -- of the cube at which the face starts.
  set v : Fin (m + 1) → I := i.insertNth t 0 with hv
  have hface : face i t (ContinuousMap.id (Fin (m + 1) → I)) 0 = v := face_id_apply_zero i t
  have hl : D.originTransport hm c ≫
      ((ContinuousMap.subtypeVal A).comp (D.retract hm c)).pathClass 0
        (face i t (ContinuousMap.id _) 0) ≍ (D.sweep c).pathClass 0 (Fin.cons 1 v) :=
    comp_heq_pathClass (D.sweep c) (D.mk_sweep_zero c) (congrArg _ (by simp [sweep_apply]))
      (congrArg _ (by simp [sweep_apply, hface]))
      (D.originTransport_heq hm c)
      ((D.pathClass_heq_sweep_retract hm c 0 _).trans (pathClass_heq rfl rfl (by rw [hface])))
  have hr₁ : c.pathClass 0 (face i t (ContinuousMap.id _) 0) ≍
      (D.sweep c).pathClass 0 (Fin.cons 0 v) :=
    (D.pathClass_heq_sweep c _ _).trans
      (pathClass_heq rfl (Matrix.cons_zero_zero) (by rw [hface]))
  have hr₂ : D.originTransport ((Nat.cast_le.2 m.le_succ).trans_lt hm)
      (c.comp (face i t (ContinuousMap.id _))) ≍
      (D.sweep c).pathClass (Fin.cons 0 v) (Fin.cons 1 v) :=
    (D.originTransport_heq _ _).trans ((pathClass_heq (D.sweep_comp_face_eq c i ht) rfl rfl).trans
      ((heq_of_eq (pathClass_comp _ _ _ _)).trans
        (pathClass_heq rfl (insertNth_succ_zero i t) (Fin.insertNth_succ_cons i t 1 0))))
  refine hl.trans (HEq.symm (comp_heq_pathClass (D.sweep c) (D.mk_sweep_zero c)
    (congrArg _ ?_) (congrArg _ ?_) hr₁ hr₂))
  · simp [sweep_apply, hface]
  · simp [sweep_apply, comp_face_id, ← D.homotopy_insertNth c i ht, hv]

/-- The track of the origin of a cube of `A` is constant. -/
theorem originTransport_subtypeVal_comp_heq {m : ℕ} (hm : (m : ℕ∞) < n) (c : SingularCube A m) :
    D.originTransport hm ((ContinuousMap.subtypeVal A).comp c) ≍
      𝟙 (FundamentalGroupoid.mk ((c 0 : A) : X)) := by
  refine (fromPath_heq_pathClass ((ContinuousMap.subtypeVal A).comp c) (Path.refl 0) _
    fun s ↦ ?_).trans (heq_of_eq (ContinuousMap.pathClass_self _ _))
  have hc : range ((ContinuousMap.subtypeVal A).comp c) ⊆ A := by
    rintro _ ⟨y, rfl⟩
    exact (c y).2
  simpa using D.homotopy_of_range_subset hc s 0

end Transport

section Chains

variable {R : Type u} [Ring R] {X : TopCat.{v}} {A : Set X} {n : ℕ∞}
  (D : SubspaceCubeDeformation A n)
  (L : LocalCoefficientSystem.{u, v, w} R X)

/-! ### The operators on unnormalized chains -/

/-- The coefficient of the end of the deformation of `c`: transport along the track of the
origin, into the fibre of the restricted system. -/
private def retractCoeff {m : ℕ} (hm : (m : ℕ∞) < n) (c : SingularCube X m) :
    L.obj (FundamentalGroupoid.mk (c 0)) →ₗ[R]
      ((pullback (X := TopCat.of A) (ContinuousMap.subtypeVal A)).obj L).obj
        (FundamentalGroupoid.mk ((D.retract hm c : SingularCube (TopCat.of A) m) 0)) :=
  (L.map (D.originTransport hm c)).hom

/-- Transport inside the end of the deformation of `c`, after the transport along the track of
its origin, is transport along their composite in `X`. -/
private theorem map_retractCoeff_heq {m : ℕ} (hm : (m : ℕ∞) < n) (c : SingularCube X m)
    {z : FundamentalGroupoid A} (q : FundamentalGroupoid.mk (D.retract hm c 0) ⟶ z)
    (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    ((pullback (X := TopCat.of A) (ContinuousMap.subtypeVal A)).obj L).map q
        (D.retractCoeff L hm c a) ≍
      L.map (D.originTransport hm c ≫ (FundamentalGroupoid.map (ContinuousMap.subtypeVal A)).map q)
        a :=
  pullback_map_map_heq (X := TopCat.of A) (ContinuousMap.subtypeVal A) L
    (y := FundamentalGroupoid.mk (D.retract hm c 0)) (D.originTransport hm c) q a

/-- The retraction onto the cubes of `A`, on unnormalized chains with local coefficients. -/
private def twistedRetract {m : ℕ} (hm : (m : ℕ∞) < n) :
    L.TwistedCubicalChain m →ₗ[R]
      ((pullback (X := TopCat.of A) (ContinuousMap.subtypeVal A)).obj L).TwistedCubicalChain m :=
  TwistedCubicalChain.desc L fun c ↦
    TwistedCubicalChain.ofCube ((pullback (X := TopCat.of A) (ContinuousMap.subtypeVal A)).obj L)
      (D.retract hm c : SingularCube (TopCat.of A) m) ∘ₗ D.retractCoeff L hm c

private theorem twistedRetract_ofCube {m : ℕ} (hm : (m : ℕ∞) < n) (c : SingularCube X m)
    (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    D.twistedRetract L hm (TwistedCubicalChain.ofCube L c a) =
      TwistedCubicalChain.ofCube ((pullback (X := TopCat.of A) (ContinuousMap.subtypeVal A)).obj L)
        (D.retract hm c : SingularCube (TopCat.of A) m) (D.retractCoeff L hm c a) :=
  TwistedCubicalChain.desc_ofCube _ c a

/-- The negative swept-cube operator, on unnormalized chains with local coefficients. -/
private def twistedPrism (m : ℕ) : L.TwistedCubicalChain m →ₗ[R] L.TwistedCubicalChain (m + 1) :=
  -TwistedCubicalChain.desc L fun c ↦
    TwistedCubicalChain.ofCube L (D.sweep c) ∘ₗ (L.map (eqToHom (D.mk_sweep_zero c))).hom

private theorem twistedPrism_ofCube {m : ℕ} (c : SingularCube X m)
    (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    D.twistedPrism L m (TwistedCubicalChain.ofCube L c a) =
      -TwistedCubicalChain.ofCube L (D.sweep c) (L.map (eqToHom (D.mk_sweep_zero c)) a) := by
  rw [twistedPrism, LinearMap.neg_apply, TwistedCubicalChain.desc_ofCube]
  rfl

private theorem twistedRetract_map_subtypeVal {m : ℕ} (hm : (m : ℕ∞) < n) :
    D.twistedRetract L hm ∘ₗ
        TwistedCubicalChain.map (X := TopCat.of A) (ContinuousMap.subtypeVal A) L m =
      LinearMap.id :=
  TwistedCubicalChain.hom_ext fun c ↦ LinearMap.ext fun a ↦ by
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    refine (congrArg _ (TwistedCubicalChain.map_ofCube c a)).trans
      ((D.twistedRetract_ofCube L hm ((ContinuousMap.subtypeVal A).comp c) a).trans
        (TwistedCubicalChain.ofCube_congr _ (D.retract_subtypeVal_comp hm c)
          ((map_apply_heq L (by rw [D.retract_subtypeVal_comp hm c])
            (D.originTransport_subtypeVal_comp_heq hm c) a).trans
              (heq_of_eq (congrArg (fun g ↦ g.hom a) (L.map_id _))))))

/-- A face of the end of the deformation, with its transported coefficient, is the retraction of
the face. -/
private theorem ofSubcube_retract {m : ℕ} (hm : ((m + 1 : ℕ) : ℕ∞) < n)
    (c : SingularCube X (m + 1)) (i : Fin (m + 1)) {t : I} (ht : t = 0 ∨ t = 1)
    (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    TwistedCubicalChain.ofSubcube
        ((pullback (X := TopCat.of A) (ContinuousMap.subtypeVal A)).obj L)
        (D.retract hm c : SingularCube (TopCat.of A) (m + 1)) (face i t (ContinuousMap.id _))
        (D.retractCoeff L hm c a) =
      D.twistedRetract L ((Nat.cast_le.2 m.le_succ).trans_lt hm)
        (TwistedCubicalChain.ofSubcube L c (face i t (ContinuousMap.id _)) a) := by
  rw [TwistedCubicalChain.ofSubcube_apply, TwistedCubicalChain.ofSubcube_apply,
    twistedRetract_ofCube]
  refine TwistedCubicalChain.ofCube_congr _ ?_ ((D.map_retractCoeff_heq L hm c _ a).trans ?_)
  · rw [comp_face_id, comp_face_id, D.face_retract hm c i ht]
  · rw [ContinuousMap.map_pathClass]
    refine (map_apply_heq L (congrArg _ ?_) (D.originTransport_comp_pathClass_heq hm c i ht)
      a).trans (heq_of_eq (by rw [L.map_comp]; rfl))
    simp [comp_face_id, ← D.homotopy_insertNth c i ht]

private theorem boundary_twistedRetract {m : ℕ} (hm : ((m + 1 : ℕ) : ℕ∞) < n) :
    TwistedCubicalChain.boundary _ m ∘ₗ D.twistedRetract L hm =
      D.twistedRetract L ((Nat.cast_le.2 m.le_succ).trans_lt hm) ∘ₗ
        TwistedCubicalChain.boundary L m :=
  TwistedCubicalChain.hom_ext fun c ↦ LinearMap.ext fun a ↦ by
    simp only [LinearMap.comp_apply, twistedRetract_ofCube]
    rw [TwistedCubicalChain.boundary_ofCube, TwistedCubicalChain.boundary_ofCube]
    simp only [map_sum, map_zsmul, map_sub]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [D.ofSubcube_retract L hm c i (Or.inl rfl), D.ofSubcube_retract L hm c i (Or.inr rfl)]

/-- The bottom face of the swept cube is the cube. -/
private theorem ofSubcube_sweep_face_zero_zero {m : ℕ} (c : SingularCube X m)
    (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    TwistedCubicalChain.ofSubcube L (D.sweep c) (face 0 0 (ContinuousMap.id _))
        (L.map (eqToHom (D.mk_sweep_zero c)) a) = TwistedCubicalChain.ofCube L c a := by
  rw [TwistedCubicalChain.ofSubcube_apply, ← ModuleCat.comp_apply, ← L.map_comp]
  refine TwistedCubicalChain.ofCube_congr L ?_ ((map_apply_heq L (congrArg _ ?_)
    (D.eqToHom_comp_pathClass_face_zero_zero_heq c) a).trans (heq_of_eq ?_))
  · rw [comp_face_id, face_zero_zero_sweep]
  · rw [← ContinuousMap.comp_apply, comp_face_id, face_zero_zero_sweep]
  · rw [L.map_id]
    rfl

/-- The top face of the swept cube is the retraction of the cube, read in `X`. -/
private theorem ofSubcube_sweep_face_zero_one {m : ℕ} (hm : (m : ℕ∞) < n) (c : SingularCube X m)
    (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    TwistedCubicalChain.ofSubcube L (D.sweep c) (face 0 1 (ContinuousMap.id _))
        (L.map (eqToHom (D.mk_sweep_zero c)) a) =
      TwistedCubicalChain.map (X := TopCat.of A) (ContinuousMap.subtypeVal A) L m
        (D.twistedRetract L hm (TwistedCubicalChain.ofCube L c a)) := by
  rw [twistedRetract_ofCube, TwistedCubicalChain.ofSubcube_apply, ← ModuleCat.comp_apply,
    ← L.map_comp]
  refine Eq.trans ?_ (TwistedCubicalChain.map_ofCube _ _).symm
  refine TwistedCubicalChain.ofCube_congr L ?_ (map_apply_heq L (congrArg _ ?_)
    (D.eqToHom_comp_pathClass_face_zero_one_heq hm c) a)
  · rw [comp_face_id, face_zero_one_sweep, subtypeVal_comp_retract]
  · rw [← ContinuousMap.comp_apply, comp_face_id, face_zero_one_sweep]
    simp

/-- The spatial faces of the swept cube are the swept faces. -/
private theorem ofSubcube_sweep_face_succ {m : ℕ} (c : SingularCube X (m + 1)) (i : Fin (m + 1))
    {t : I} (ht : t = 0 ∨ t = 1) (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    TwistedCubicalChain.ofSubcube L (D.sweep c) (face i.succ t (ContinuousMap.id _))
        (L.map (eqToHom (D.mk_sweep_zero c)) a) =
      -D.twistedPrism L m
        (TwistedCubicalChain.ofSubcube L c (face i t (ContinuousMap.id _)) a) := by
  rw [TwistedCubicalChain.ofSubcube_apply, ← ModuleCat.comp_apply, ← L.map_comp,
    TwistedCubicalChain.ofSubcube_apply, twistedPrism_ofCube, neg_neg, ← ModuleCat.comp_apply,
    ← L.map_comp]
  have h : (D.sweep c).comp (face i.succ t (ContinuousMap.id _)) =
      D.sweep (c.comp (face i t (ContinuousMap.id _))) := by
    rw [comp_face_id, comp_face_id, D.face_succ_sweep c i ht]
  exact TwistedCubicalChain.ofCube_congr L h
    (map_apply_heq L (congrArg (fun d ↦ FundamentalGroupoid.mk (d 0)) h)
      (D.eqToHom_comp_pathClass_face_succ_heq c i t) a)

/-- The prism identity `∂ P + P ∂ = ι ρ - id` on unnormalized chains, in positive degrees. -/
private theorem boundary_twistedPrism_add_twistedPrism_boundary {m : ℕ}
    (hm : ((m + 1 : ℕ) : ℕ∞) < n) :
    TwistedCubicalChain.boundary L (m + 1) ∘ₗ D.twistedPrism L (m + 1) +
        D.twistedPrism L m ∘ₗ TwistedCubicalChain.boundary L m =
      TwistedCubicalChain.map (X := TopCat.of A) (ContinuousMap.subtypeVal A) L (m + 1) ∘ₗ
        D.twistedRetract L hm - LinearMap.id :=
  TwistedCubicalChain.hom_ext fun c ↦ LinearMap.ext fun a ↦ by
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.id_apply, twistedPrism_ofCube, map_neg, TwistedCubicalChain.boundary_ofCube,
      map_sum, map_zsmul, map_sub]
    rw [Fin.sum_univ_succ]
    simp only [ofSubcube_sweep_face_zero_zero, D.ofSubcube_sweep_face_zero_one L hm,
      D.ofSubcube_sweep_face_succ L c _ (Or.inl rfl),
      D.ofSubcube_sweep_face_succ L c _ (Or.inr rfl),
      Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ, mul_neg_one, neg_smul, smul_neg,
      smul_sub, neg_neg]
    abel

/-- The prism identity `∂ P = ι ρ - id` on unnormalized chains, in degree zero. -/
private theorem boundary_twistedPrism_zero (hm : ((0 : ℕ) : ℕ∞) < n) :
    TwistedCubicalChain.boundary L 0 ∘ₗ D.twistedPrism L 0 =
      TwistedCubicalChain.map (X := TopCat.of A) (ContinuousMap.subtypeVal A) L 0 ∘ₗ
        D.twistedRetract L hm - LinearMap.id :=
  TwistedCubicalChain.hom_ext fun c ↦ LinearMap.ext fun a ↦ by
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, twistedPrism_ofCube,
      map_neg, TwistedCubicalChain.boundary_ofCube, Fin.sum_univ_succ, Fin.sum_univ_zero,
      add_zero, Fin.val_zero, pow_zero, one_smul, ofSubcube_sweep_face_zero_zero,
      D.ofSubcube_sweep_face_zero_one L hm, neg_sub]

/-! ### The operators on normalized chains -/

/-- **The retraction onto the cubes of `A`** on normalized cubical chains with coefficients in
`L`: the end of the deformation of a cube, carrying the coefficient transported along the track of
the origin of the cube, in the restriction of `L` to `A`. -/
def twistedRetractChain {m : ℕ} (hm : (m : ℕ∞) < n) :
    L.NormalizedTwistedCubicalChain m →ₗ[R]
      ((pullback (X := TopCat.of A) (ContinuousMap.subtypeVal A)).obj
        L).NormalizedTwistedCubicalChain m :=
  Submodule.mapQ _ _ (D.twistedRetract L hm) (TwistedCubicalChain.degenerate_le fun c hc a ↦ by
    rw [Submodule.mem_comap, twistedRetract_ofCube]
    exact TwistedCubicalChain.ofCube_mem_degenerate (D.isDegenerate_retract hm hc) _)

/-- The retraction sends a cube with a coefficient to the end of the deformation of the cube, with
the coefficient transported along the track of the origin. -/
@[simp]
theorem twistedRetractChain_ofCube {m : ℕ} (hm : (m : ℕ∞) < n) (c : SingularCube X m)
    (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    D.twistedRetractChain L hm (NormalizedTwistedCubicalChain.ofCube L c a) =
      NormalizedTwistedCubicalChain.ofCube
        ((pullback (X := TopCat.of A) (ContinuousMap.subtypeVal A)).obj L)
        (D.retract hm c : SingularCube (TopCat.of A) m) (L.map (D.originTransport hm c) a) := by
  rw [NormalizedTwistedCubicalChain.ofCube_apply, twistedRetractChain, Submodule.mapQ_apply,
    twistedRetract_ofCube]
  exact (NormalizedTwistedCubicalChain.ofCube_apply _ _).symm

/-- The negative swept-cube operator on normalized cubical chains with coefficients in `L`. -/
def twistedPrismChain (m : ℕ) :
    L.NormalizedTwistedCubicalChain m →ₗ[R] L.NormalizedTwistedCubicalChain (m + 1) :=
  Submodule.mapQ _ _ (D.twistedPrism L m) (TwistedCubicalChain.degenerate_le fun c hc a ↦ by
    rw [Submodule.mem_comap, twistedPrism_ofCube]
    exact neg_mem (TwistedCubicalChain.ofCube_mem_degenerate (D.isDegenerate_sweep hc) _))

/-- The swept-cube operator sends a cube with a coefficient to the negative of its swept cube,
which starts at the origin of the cube and carries the same coefficient. -/
@[simp]
theorem twistedPrismChain_ofCube {m : ℕ} (c : SingularCube X m)
    (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    D.twistedPrismChain L m (NormalizedTwistedCubicalChain.ofCube L c a) =
      -NormalizedTwistedCubicalChain.ofCube L (D.sweep c)
        (L.map (eqToHom (congrArg FundamentalGroupoid.mk (D.sweep_apply_zero c).symm)) a) := by
  rw [NormalizedTwistedCubicalChain.ofCube_apply, twistedPrismChain, Submodule.mapQ_apply,
    twistedPrism_ofCube, NormalizedTwistedCubicalChain.ofCube_apply, Submodule.Quotient.mk_neg]

/-- **The retraction is a left inverse of the inclusion** on normalized cubical chains with local
coefficients, since the deformation fixes the cubes of `A`. -/
@[simp]
theorem twistedRetractChain_map_subtypeVal {m : ℕ} (hm : (m : ℕ∞) < n)
    (g : ((pullback (X := TopCat.of A) (ContinuousMap.subtypeVal A)).obj
      L).NormalizedTwistedCubicalChain m) :
    D.twistedRetractChain L hm
      (NormalizedTwistedCubicalChain.map (X := TopCat.of A) (ContinuousMap.subtypeVal A) L m g) =
        g := by
  refine Submodule.Quotient.induction_on _ g fun x ↦ ?_
  simp only [twistedRetractChain, Submodule.mapQ_apply, NormalizedTwistedCubicalChain.map_mk,
    ← LinearMap.comp_apply, D.twistedRetract_map_subtypeVal L hm, LinearMap.id_apply]

/-- The retraction commutes with the boundary. -/
theorem boundary_twistedRetractChain {m : ℕ} (hm : ((m + 1 : ℕ) : ℕ∞) < n)
    (g : L.NormalizedTwistedCubicalChain (m + 1)) :
    NormalizedTwistedCubicalChain.boundary _ m (D.twistedRetractChain L hm g) =
      D.twistedRetractChain L ((Nat.cast_le.2 m.le_succ).trans_lt hm)
        (NormalizedTwistedCubicalChain.boundary L m g) := by
  refine Submodule.Quotient.induction_on _ g fun x ↦ ?_
  have h := LinearMap.congr_fun (D.boundary_twistedRetract L hm) x
  simp only [LinearMap.comp_apply] at h
  simp only [twistedRetractChain, Submodule.mapQ_apply, NormalizedTwistedCubicalChain.boundary_mk,
    h]

/-- **The prism identity** `∂ P + P ∂ = ι ρ - id` in positive degrees, for the swept-cube operator
`P`, the retraction `ρ` and the inclusion `ι` of `A`. -/
theorem boundary_twistedPrismChain_add_twistedPrismChain_boundary {m : ℕ}
    (hm : ((m + 1 : ℕ) : ℕ∞) < n) (g : L.NormalizedTwistedCubicalChain (m + 1)) :
    NormalizedTwistedCubicalChain.boundary L (m + 1) (D.twistedPrismChain L (m + 1) g) +
        D.twistedPrismChain L m (NormalizedTwistedCubicalChain.boundary L m g) =
      NormalizedTwistedCubicalChain.map (X := TopCat.of A) (ContinuousMap.subtypeVal A) L (m + 1)
        (D.twistedRetractChain L hm g) - g := by
  refine Submodule.Quotient.induction_on _ g fun x ↦ ?_
  have h := LinearMap.congr_fun (D.boundary_twistedPrism_add_twistedPrism_boundary L hm) x
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.id_apply] at h
  simp only [twistedPrismChain, twistedRetractChain, Submodule.mapQ_apply,
    NormalizedTwistedCubicalChain.boundary_mk, NormalizedTwistedCubicalChain.map_mk,
    ← Submodule.Quotient.mk_add, ← Submodule.Quotient.mk_sub, h]

/-- The prism identity `∂ P = ι ρ - id` in degree zero. -/
theorem boundary_twistedPrismChain_zero (hm : ((0 : ℕ) : ℕ∞) < n)
    (g : L.NormalizedTwistedCubicalChain 0) :
    NormalizedTwistedCubicalChain.boundary L 0 (D.twistedPrismChain L 0 g) =
      NormalizedTwistedCubicalChain.map (X := TopCat.of A) (ContinuousMap.subtypeVal A) L 0
        (D.twistedRetractChain L hm g) - g := by
  refine Submodule.Quotient.induction_on _ g fun x ↦ ?_
  have h := LinearMap.congr_fun (D.boundary_twistedPrism_zero L hm) x
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply] at h
  simp only [twistedPrismChain, twistedRetractChain, Submodule.mapQ_apply,
    NormalizedTwistedCubicalChain.boundary_mk, NormalizedTwistedCubicalChain.map_mk,
    ← Submodule.Quotient.mk_sub, h]

end Chains

/-! ### The chain homotopy equivalence of normalized cubical chain complexes -/

section ChainComplex

variable {R : Type u} [Ring R] {X : TopCat.{v}} {A : Set X} (D : SubspaceCubeDeformation A ⊤)
  (L : LocalCoefficientSystem.{u, v, w} R X)

/-- The retraction onto the cubes of `A`, as a chain map from the normalized cubical chains of `X`
with coefficients in `L` to those of `A` with coefficients in the restriction of `L`. -/
def twistedRetractChainMap :
    L.normalizedTwistedCubicalChainComplex ⟶
      ((pullback (X := TopCat.of A) (ContinuousMap.subtypeVal A)).obj
        L).normalizedTwistedCubicalChainComplex :=
  ChainComplex.ofHom (fun m ↦ ModuleCat.ofHom (D.twistedRetractChain L (ENat.natCast_lt_top m)))
    fun m ↦ by
    ext g
    exact (normalizedTwistedCubicalChainComplex_d_apply _ m _).trans
      ((D.boundary_twistedRetractChain L (ENat.natCast_lt_top (m + 1)) g).trans
        (congrArg _ (normalizedTwistedCubicalChainComplex_d_apply L m g).symm))

/-- The components of the retraction chain map. -/
@[simp]
theorem twistedRetractChainMap_f (m : ℕ) :
    (D.twistedRetractChainMap L).f m =
      ModuleCat.ofHom (D.twistedRetractChain L (ENat.natCast_lt_top m)) := by
  unfold twistedRetractChainMap
  rfl

/-- The retraction chain map is a left inverse of the chain map induced by the inclusion of
`A`. -/
@[reassoc (attr := simp)]
theorem normalizedTwistedCubicalChainComplexMap_comp_twistedRetractChainMap :
    normalizedTwistedCubicalChainComplexMap (X := TopCat.of A) (ContinuousMap.subtypeVal A) L ≫
      D.twistedRetractChainMap L = 𝟙 _ := by
  ext m g
  -- In degree `m` both chain maps act by their concrete linear maps, and the terms of the
  -- normalized cubical chain complex are the modules of normalized chains by definition
  -- (`normalizedTwistedCubicalChainComplex_X`), so the goal is the chain-level statement.
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
    normalizedTwistedCubicalChainComplexMap_f, twistedRetractChainMap_f, ModuleCat.hom_id,
    LinearMap.id_apply]
  exact D.twistedRetractChain_map_subtypeVal L (ENat.natCast_lt_top m) g

/-- The negative swept-cube operator, as a morphism between the terms of the normalized cubical
chain complex. -/
private def twistedPrismHom (m : ℕ) :
    L.normalizedTwistedCubicalChainComplex.X m ⟶ L.normalizedTwistedCubicalChainComplex.X (m + 1) :=
  ModuleCat.ofHom (D.twistedPrismChain L m)

/-- **The chain homotopy from the identity to the composite of the retraction and the inclusion of
`A`**, given in degree `m` by the swept-cube operator `-D.twistedPrismChain L m`. -/
def twistedRetractHomotopy :
    Homotopy (𝟙 _) (D.twistedRetractChainMap L ≫
      normalizedTwistedCubicalChainComplexMap (X := TopCat.of A) (ContinuousMap.subtypeVal A) L) :=
  (Homotopy.equivSubZero.symm
    (Homotopy.mkChainComplex (D.twistedRetractChainMap L ≫
        normalizedTwistedCubicalChainComplexMap (X := TopCat.of A) (ContinuousMap.subtypeVal A) L -
          𝟙 _)
      (D.twistedPrismHom L)
      (by
        ext g
        have h := normalizedTwistedCubicalChainComplex_d_apply L 0 (D.twistedPrismHom L 0 g)
        simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.comp_f,
          HomologicalComplex.id_f, ModuleCat.hom_sub, ModuleCat.hom_id, ModuleCat.hom_comp,
          LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
          normalizedTwistedCubicalChainComplexMap_f, twistedRetractChainMap_f]
        rw [h]
        exact (D.boundary_twistedPrismChain_zero L (ENat.natCast_lt_top 0) g).symm)
      (fun m ↦ by
        ext g
        -- The differentials of `ChainComplex.of` are the boundaries only after `ChainComplex.of_d`.
        have h₁ := normalizedTwistedCubicalChainComplex_d_apply L m g
        have h₂ := normalizedTwistedCubicalChainComplex_d_apply L (m + 1)
          (D.twistedPrismHom L (m + 1) g)
        simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.comp_f,
          HomologicalComplex.id_f, ModuleCat.hom_sub, ModuleCat.hom_id, ModuleCat.hom_add,
          ModuleCat.hom_comp, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.add_apply,
          LinearMap.comp_apply, normalizedTwistedCubicalChainComplexMap_f,
          twistedRetractChainMap_f]
        rw [h₁, h₂]
        exact (D.boundary_twistedPrismChain_add_twistedPrismChain_boundary L
          (ENat.natCast_lt_top (m + 1)) g).symm.trans
          (add_comm _ _))))
    |>.symm

/-- The chain homotopy is the swept-cube operator. -/
@[simp]
theorem twistedRetractHomotopy_hom_succ (m : ℕ) (g : L.NormalizedTwistedCubicalChain m) :
    (D.twistedRetractHomotopy L).hom m (m + 1) g = -D.twistedPrismChain L m g := by
  simp only [twistedRetractHomotopy, Homotopy.symm_hom, Homotopy.equivSubZero,
    Equiv.coe_fn_symm_mk]
  rw [Homotopy.mkChainComplex_hom_succ]
  -- `twistedPrismHom` is `twistedPrismChain` viewed as a morphism of modules, so this holds by
  -- definition.
  rfl

/-- **The inclusion of `A` induces a chain homotopy equivalence of normalized cubical chains with
local coefficients**, from the chains of `A` with coefficients in the restriction of `L` to the
chains of `X` with coefficients in `L`, with the retraction as homotopy inverse. -/
def normalizedTwistedCubicalChainComplexHomotopyEquiv :
    HomotopyEquiv
      ((pullback (X := TopCat.of A) (ContinuousMap.subtypeVal A)).obj
        L).normalizedTwistedCubicalChainComplex
      L.normalizedTwistedCubicalChainComplex where
  hom := normalizedTwistedCubicalChainComplexMap (X := TopCat.of A) (ContinuousMap.subtypeVal A) L
  inv := D.twistedRetractChainMap L
  homotopyHomInvId :=
    Homotopy.ofEq (D.normalizedTwistedCubicalChainComplexMap_comp_twistedRetractChainMap L)
  homotopyInvHomId := (D.twistedRetractHomotopy L).symm

@[simp]
theorem normalizedTwistedCubicalChainComplexHomotopyEquiv_hom :
    (D.normalizedTwistedCubicalChainComplexHomotopyEquiv L).hom =
      normalizedTwistedCubicalChainComplexMap (X := TopCat.of A) (ContinuousMap.subtypeVal A) L :=
  (rfl)

@[simp]
theorem normalizedTwistedCubicalChainComplexHomotopyEquiv_inv :
    (D.normalizedTwistedCubicalChainComplexHomotopyEquiv L).inv = D.twistedRetractChainMap L :=
  (rfl)

/-- **The inclusion of `A` induces a quasi-isomorphism of normalized cubical chains with local
coefficients.** -/
theorem quasiIso_normalizedTwistedCubicalChainComplexMap (D : SubspaceCubeDeformation A ⊤) :
    QuasiIso
      (normalizedTwistedCubicalChainComplexMap (X := TopCat.of A) (ContinuousMap.subtypeVal A) L) :=
  inferInstanceAs (QuasiIso (D.normalizedTwistedCubicalChainComplexHomotopyEquiv L).hom)

end ChainComplex

/-! ### Homology below the dimension bound of the deformation -/

section Homology

variable {R : Type u} [Ring R] {X : TopCat.{v}} {A : Set X} {n : ℕ∞}
  (L : LocalCoefficientSystem.{u, v, w} R X)

/-- **Below the dimension bound of a deformation into `A`, the inclusion of `A` is surjective on
homology with local coefficients**: if the singular cubes of `X` deform into `A` below dimension
`n`, then `H_m(A; L|_A) ⟶ H_m(X; L)` is an epimorphism on normalized cubical homology for every
`m < n`. -/
theorem epi_homologyMap_normalizedTwistedCubicalChainComplexMap (D : SubspaceCubeDeformation A n)
    {m : ℕ} (hm : (m : ℕ∞) < n) :
    Epi (HomologicalComplex.homologyMap
      (normalizedTwistedCubicalChainComplexMap (X := TopCat.of A) (ContinuousMap.subtypeVal A) L)
        m) := by
  -- A cycle `y` is the image of the cycle `ρ y`, up to the boundary of the swept chain `-P y`.
  cases m with
  | zero =>
    rw [HomologicalComplex.moduleCat_epi_homologyMap_iff _ (ChainComplex.prev ℕ 0)
      ChainComplex.next_nat_zero]
    intro (y : L.NormalizedTwistedCubicalChain 0) _
    refine ⟨D.twistedRetractChain L hm y, ?_, -D.twistedPrismChain L 0 y, ?_⟩
    · -- No differential leaves degree zero.
      rw [HomologicalComplex.shape _ _ _ (by simp)]
      rfl
    · refine (normalizedTwistedCubicalChainComplex_d_apply L 0 _).trans ?_
      rw [map_neg, D.boundary_twistedPrismChain_zero L hm, neg_sub,
        normalizedTwistedCubicalChainComplexMap_f]
      -- `ModuleCat.ofHom` of a linear map applies that linear map, by definition.
      rfl
  | succ k =>
    rw [HomologicalComplex.moduleCat_epi_homologyMap_iff _ (ChainComplex.prev ℕ (k + 1))
      (ChainComplex.next_nat_succ k)]
    intro (y : L.NormalizedTwistedCubicalChain (k + 1)) hy
    have hy' : NormalizedTwistedCubicalChain.boundary L k y = 0 :=
      (normalizedTwistedCubicalChainComplex_d_apply L k y).symm.trans hy
    refine ⟨D.twistedRetractChain L hm y, ?_, -D.twistedPrismChain L (k + 1) y, ?_⟩
    · refine (normalizedTwistedCubicalChainComplex_d_apply _ k _).trans ?_
      rw [D.boundary_twistedRetractChain L hm, hy', map_zero]
      -- The zero chain is the zero of the term of the complex, by definition.
      rfl
    · have h := D.boundary_twistedPrismChain_add_twistedPrismChain_boundary L hm y
      rw [hy', map_zero, add_zero] at h
      refine (normalizedTwistedCubicalChainComplex_d_apply L (k + 1) _).trans ?_
      rw [map_neg, h, neg_sub, normalizedTwistedCubicalChainComplexMap_f]
      -- `ModuleCat.ofHom` of a linear map applies that linear map, by definition.
      rfl

/-- **One degree below the dimension bound of a deformation into `A`, the inclusion of `A` is an
isomorphism on homology with local coefficients**: if the singular cubes of `X` deform into `A`
below dimension `n`, then `H_m(A; L|_A) ⟶ H_m(X; L)` is an isomorphism on normalized cubical
homology for every `m + 1 < n`. -/
theorem quasiIsoAt_normalizedTwistedCubicalChainComplexMap (D : SubspaceCubeDeformation A n)
    {m : ℕ} (hm : ((m + 1 : ℕ) : ℕ∞) < n) :
    QuasiIsoAt
      (normalizedTwistedCubicalChainComplexMap (X := TopCat.of A) (ContinuousMap.subtypeVal A) L)
        m := by
  -- If the image of a cycle `x` bounds `b` in `X`, then `x` bounds the retraction `ρ b` in `A`.
  have hinj (x : ((pullback (X := TopCat.of A) (ContinuousMap.subtypeVal A)).obj
      L).NormalizedTwistedCubicalChain m) (b : L.NormalizedTwistedCubicalChain (m + 1))
      (hb : NormalizedTwistedCubicalChain.boundary L m b =
        NormalizedTwistedCubicalChain.map (X := TopCat.of A) (ContinuousMap.subtypeVal A) L m x) :
      NormalizedTwistedCubicalChain.boundary _ m (D.twistedRetractChain L hm b) = x := by
    rw [D.boundary_twistedRetractChain L hm, hb]
    exact D.twistedRetractChain_map_subtypeVal L _ x
  have hepi := D.epi_homologyMap_normalizedTwistedCubicalChainComplexMap L
    ((Nat.cast_le.2 m.le_succ).trans_lt hm)
  rw [HomologicalComplex.moduleCat_epi_homologyMap_iff _ (ChainComplex.prev ℕ m) rfl] at hepi
  rw [HomologicalComplex.moduleCat_quasiIsoAt_iff _ (ChainComplex.prev ℕ m) rfl]
  exact ⟨hepi, fun x _ b hb ↦ ⟨D.twistedRetractChain L hm b,
    (normalizedTwistedCubicalChainComplex_d_apply _ m _).trans
      (hinj x b ((normalizedTwistedCubicalChainComplex_d_apply L m b).symm.trans
        -- `ModuleCat.ofHom` of a linear map applies that linear map, by definition.
        (hb.trans (by rw [normalizedTwistedCubicalChainComplexMap_f]; rfl))))⟩⟩

end Homology

end SubspaceCubeDeformation

/-- **The inclusion of a subspace with vanishing relative homotopy sets induces a quasi-isomorphism
of normalized cubical chains with local coefficients.** If every point of `X` is joined by a path
to a point of `A`, and the relative homotopy set `π_{n+1}(X, A, a)` is trivial for every `n` and
every `a ∈ A`, then for every local coefficient system `L` on `X` the inclusion of `A` induces
isomorphisms `H_n(A; L|_A) ≅ H_n(X; L)` on normalized cubical homology with local
coefficients. -/
theorem quasiIso_normalizedTwistedCubicalChainComplexMap_subtypeVal_of_relHomotopyGroup
    {R : Type u} [Ring R] {X : TopCat.{v}} {A : Set X} (h₀ : ∀ x : X, ∃ a ∈ A, Joined x a)
    (h : ∀ (n : ℕ) (a : A), Subsingleton (RelHomotopyGroup (Fin n) ⟨TopPair.ofSubset A, a⟩))
    (L : LocalCoefficientSystem.{u, v, w} R X) :
    QuasiIso
      (normalizedTwistedCubicalChainComplexMap (X := TopCat.of A) (ContinuousMap.subtypeVal A) L) :=
  (nonempty_subspaceCubeDeformation_of_relHomotopyGroup h₀ fun k _ ↦ h k).some
    |>.quasiIso_normalizedTwistedCubicalChainComplexMap L

/-- **The inclusion of a subspace is surjective on homology with local coefficients below the
connectivity of the pair.** If every point of `X` is joined by a path to a point of `A`, and the
relative homotopy set `π_{k+1}(X, A, a)` is trivial for every `k + 1 < n` and every `a ∈ A`, then
for every local coefficient system `L` on `X` the inclusion of `A` induces an epimorphism
`H_m(A; L|_A) ⟶ H_m(X; L)` for every `m < n`. -/
theorem epi_twistedHomologyMap_subtypeVal_of_relHomotopyGroup {R : Type u} [Ring R]
    {X : TopCat.{v}} {A : Set X} {n : ℕ} (h₀ : ∀ x : X, ∃ a ∈ A, Joined x a)
    (h : ∀ k : ℕ, k + 1 < n → ∀ a : A,
      Subsingleton (RelHomotopyGroup (Fin k) ⟨TopPair.ofSubset A, a⟩))
    (L : LocalCoefficientSystem.{u, v, v} R X) {m : ℕ} (hm : m < n) :
    Epi (twistedHomologyMap (TopCat.ofHom (ContinuousMap.subtypeVal A)) L m) := by
  obtain ⟨D⟩ := nonempty_subspaceCubeDeformation_of_relHomotopyGroup (n := n) h₀ fun k hk ↦
    h k (by exact_mod_cast hk)
  let i : TopCat.of A ⟶ X := TopCat.ofHom (ContinuousMap.subtypeVal A)
  have : Epi (HomologicalComplex.homologyMap
      (normalizedTwistedCubicalChainComplexMap i.hom L) m) :=
    D.epi_homologyMap_normalizedTwistedCubicalChainComplexMap L (by exact_mod_cast hm)
  -- Transport the cubical statement along the comparison with simplicial chains, which is natural
  -- in the space and a quasi-isomorphism.
  have hc := congrArg (HomologicalComplex.homologyMap · m)
    (twistedCubicalToSingularMap_naturality i L)
  simp only [HomologicalComplex.homologyMap_comp] at hc
  have : Epi (HomologicalComplex.homologyMap
      (twistedCubicalToSingularMap ((LocalCoefficientSystem.pullback i.hom).obj L)) m ≫
        twistedHomologyMap i L m) := by
    rw [twistedHomologyMap, ← hc]
    infer_instance
  exact epi_of_epi (HomologicalComplex.homologyMap
    (twistedCubicalToSingularMap ((LocalCoefficientSystem.pullback i.hom).obj L)) m) _

/-- **The inclusion of a subspace is an isomorphism on homology with local coefficients one degree
below the connectivity of the pair.** If every point of `X` is joined by a path to a point of
`A`, and the relative homotopy set `π_{k+1}(X, A, a)` is trivial for every `k + 1 < n` and every
`a ∈ A`, then for every local coefficient system `L` on `X` the inclusion of `A` induces an
isomorphism `H_m(A; L|_A) ≅ H_m(X; L)` for every `m + 1 < n`. -/
theorem isIso_twistedHomologyMap_subtypeVal_of_relHomotopyGroup_of_add_one_lt
    {R : Type u} [Ring R] {X : TopCat.{v}} {A : Set X} {n : ℕ} (h₀ : ∀ x : X, ∃ a ∈ A, Joined x a)
    (h : ∀ k : ℕ, k + 1 < n → ∀ a : A,
      Subsingleton (RelHomotopyGroup (Fin k) ⟨TopPair.ofSubset A, a⟩))
    (L : LocalCoefficientSystem.{u, v, v} R X) {m : ℕ} (hm : m + 1 < n) :
    IsIso (twistedHomologyMap (TopCat.ofHom (ContinuousMap.subtypeVal A)) L m) := by
  obtain ⟨D⟩ := nonempty_subspaceCubeDeformation_of_relHomotopyGroup (n := n) h₀ fun k hk ↦
    h k (by exact_mod_cast hk)
  let i : TopCat.of A ⟶ X := TopCat.ofHom (ContinuousMap.subtypeVal A)
  have : IsIso (HomologicalComplex.homologyMap
      (normalizedTwistedCubicalChainComplexMap i.hom L) m) := by
    have := D.quasiIsoAt_normalizedTwistedCubicalChainComplexMap L (m := m)
      (by exact_mod_cast hm)
    rwa [quasiIsoAt_iff_isIso_homologyMap] at this
  -- Transport the cubical statement along the comparison with simplicial chains, which is natural
  -- in the space and a quasi-isomorphism.
  have hc := congrArg (HomologicalComplex.homologyMap · m)
    (twistedCubicalToSingularMap_naturality i L)
  simp only [HomologicalComplex.homologyMap_comp] at hc
  have : IsIso (HomologicalComplex.homologyMap
      (twistedCubicalToSingularMap ((LocalCoefficientSystem.pullback i.hom).obj L)) m ≫
        twistedHomologyMap i L m) := by
    rw [twistedHomologyMap, ← hc]
    infer_instance
  exact IsIso.of_isIso_comp_left (HomologicalComplex.homologyMap
    (twistedCubicalToSingularMap ((LocalCoefficientSystem.pullback i.hom).obj L)) m) _

end TauCeti
