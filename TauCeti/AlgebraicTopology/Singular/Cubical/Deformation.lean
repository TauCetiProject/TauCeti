/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Homotopy
public import TauCeti.AlgebraicTopology.Singular.Cubical.ChainComplex
public import TauCeti.AlgebraicTopology.Singular.Cubical.Prism

/-!
# Deformations of singular cubes and the chain homotopies they induce

A `TauCeti.CubeDeformation X` is a homotopy of every singular cube `c` of a space `X`, with time as
the first coordinate, starting at `c`, compatible with faces and degeneracies: the homotopy of a
face of `c` is the restriction of the homotopy of `c`, and the homotopy of a cube not depending on
a coordinate does not depend on it either. Deformations of the singular cubes into a prescribed
kind of cube, such as the cubes sending a skeleton to a base point
(`TauCeti.BasedCubeDeformation`) or the cubes with values in a subspace
(`TauCeti.SubspaceCubeDeformation`), extend this structure. This file turns a deformation into
chain-level data on Massey's normalized cubical chains, independently of where the cubes are
deformed to.

* The end of the homotopy of `c` is a cube `D.endCube c`. It commutes with faces and preserves
  degeneracies, so it induces a chain endomorphism `D.endChainMap R` of the normalized cubical
  chains of `X`.
* The homotopy of `c`, with time as the first coordinate, sweeps out the cube `D.sweep c` of one
  dimension more. Its first two faces are `c` and `D.endCube c`, and its other faces are the swept
  faces of `c`. The negative swept-cube operator `D.prismChain R` therefore satisfies
  `∂ P + P ∂ = ε - id` for the end `ε` of the deformation, so the swept-cube operator
  `-D.prismChain R` is a chain homotopy `D.endHomotopy R` from the identity to `D.endChainMap R`.

In particular the end of a deformation induces the identity on normalized cubical homology.
Applied to the deformations of the singular cubes into based cubes and into a compressible
subspace, this gives the vanishing of the low-degree homology of a highly connected space and the
invariance of homology under weak homotopy equivalences.

## Main definitions

* `TauCeti.CubeDeformation`: a deformation of the singular cubes of a space, compatible with faces
  and degeneracies.
* `TauCeti.CubeDeformation.endCube`, `TauCeti.CubeDeformation.cubeHomotopy`,
  `TauCeti.CubeDeformation.sweep`: the end of the deformation of a cube, the deformation as a
  homotopy, and the cube it sweeps out (its `SingularCube.prism`).
* `TauCeti.CubeDeformation.endChain`, `TauCeti.CubeDeformation.prismChain`: the induced operators
  on normalized cubical chains.
* `TauCeti.CubeDeformation.endChainMap`, `TauCeti.CubeDeformation.endHomotopy`: the end of the
  deformation as an endomorphism of the normalized cubical chain complex, and the chain homotopy
  from the identity to it.

## Main results

* `TauCeti.CubeDeformation.boundary_prismChain_add_prismChain_boundary`: the prism identity
  `∂ P + P ∂ = ε - id`.

## References

* S. Eilenberg, *Singular homology theory*, Ann. of Math. (2) 45 (1944), 407–447, for the
  deformation of singular chains into a subcomplex.
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter II, for normalized
  cubical chains and their prism operators.
-/

public section

noncomputable section

open CategoryTheory unitInterval Finsupp

namespace TauCeti

section Cubes

/-- A **deformation of the singular cubes of `X`**: a homotopy of every singular cube `c`, with time
as the first coordinate, starting at `c`, compatible with faces and degeneracies. -/
structure CubeDeformation (X : Type*) [TopologicalSpace X] where
  /-- The homotopy deforming the singular cube `c`. -/
  homotopy {m : ℕ} (c : SingularCube X m) : C(I × (Fin m → I), X)
  /-- The homotopy of `c` starts at `c`. -/
  homotopy_zero {m : ℕ} (c : SingularCube X m) (y : Fin m → I) : homotopy c (0, y) = c y
  /-- The homotopy of a face of `c` is the restriction of the homotopy of `c` to that face. -/
  homotopy_insertNth {m : ℕ} (c : SingularCube X (m + 1)) (i : Fin (m + 1)) {t : I}
    (ht : t = 0 ∨ t = 1) (s : I) (z : Fin m → I) :
    homotopy c (s, i.insertNth t z) = homotopy (SingularCube.face i t c) (s, z)
  /-- If `c` does not depend on a coordinate, then neither does its homotopy at any time. -/
  isDegenerateAt_curry {m : ℕ} {c : SingularCube X m} {i : Fin m} (hc : c.IsDegenerateAt i)
    (s : I) : SingularCube.IsDegenerateAt ((homotopy c).curry s) i

attribute [simp] CubeDeformation.homotopy_zero CubeDeformation.homotopy_insertNth

variable {X : Type*} [TopologicalSpace X]

namespace CubeDeformation

variable (D : CubeDeformation X)

/-! ### The end of the deformation and the swept cube -/

/-- The cube at the end of the deformation of the singular cube `c`. -/
def endCube {m : ℕ} (c : SingularCube X m) : SingularCube X m :=
  (D.homotopy c).curry 1

@[simp]
theorem endCube_apply {m : ℕ} (c : SingularCube X m) (y : Fin m → I) :
    D.endCube c y = D.homotopy c (1, y) :=
  (rfl)

/-- The end of the deformation commutes with the faces at the endpoints of the interval. -/
theorem face_endCube {m : ℕ} (c : SingularCube X (m + 1)) (i : Fin (m + 1)) {t : I}
    (ht : t = 0 ∨ t = 1) :
    SingularCube.face i t (D.endCube c) = D.endCube (SingularCube.face i t c) := by
  ext y
  simp [D.homotopy_insertNth c i ht]

/-- If `c` does not depend on its coordinate `i`, then neither does the end of its
deformation. -/
theorem isDegenerateAt_endCube {m : ℕ} {c : SingularCube X m} {i : Fin m}
    (hc : c.IsDegenerateAt i) : (D.endCube c).IsDegenerateAt i :=
  D.isDegenerateAt_curry hc 1

/-- The end of the deformation of a degenerate cube is degenerate. -/
theorem isDegenerate_endCube {m : ℕ} {c : SingularCube X m} (hc : c.IsDegenerate) :
    (D.endCube c).IsDegenerate :=
  (SingularCube.isDegenerate_iff.1 hc).elim fun _ hi ↦ (D.isDegenerateAt_endCube hi).isDegenerate

/-- The deformation of the singular cube `c`, as a homotopy from `c` to the cube `D.endCube c`. -/
def cubeHomotopy {m : ℕ} (c : SingularCube X m) : ContinuousMap.Homotopy c (D.endCube c) where
  toContinuousMap := D.homotopy c
  map_zero_left := D.homotopy_zero c
  map_one_left _ := rfl

@[simp]
theorem cubeHomotopy_apply {m : ℕ} (c : SingularCube X m) (p : I × (Fin m → I)) :
    D.cubeHomotopy c p = D.homotopy c p :=
  (rfl)

/-- The cube swept out by the deformation of the singular cube `c`, with time as the first
coordinate. -/
def sweep {m : ℕ} (c : SingularCube X m) : SingularCube X (m + 1) :=
  SingularCube.prism (D.cubeHomotopy c) (ContinuousMap.id _)

@[simp]
theorem sweep_apply {m : ℕ} (c : SingularCube X m) (y : Fin (m + 1) → I) :
    D.sweep c y = D.homotopy c (y 0, Fin.tail y) := by
  simp [sweep]

/-- The swept cube starts at the origin of `c`. -/
theorem sweep_apply_zero {m : ℕ} (c : SingularCube X m) : D.sweep c 0 = c 0 := by
  rw [sweep_apply, Pi.zero_apply, D.homotopy_zero]
  -- `Fin.tail 0` is the zero vector, coordinatewise by definition.
  exact congrArg c (funext fun _ ↦ rfl)

/-- The swept cube starts at `c`. -/
@[simp]
theorem face_zero_zero_sweep {m : ℕ} (c : SingularCube X m) :
    SingularCube.face 0 0 (D.sweep c) = c := by
  simp [sweep]

/-- The swept cube ends at the end of the deformation of `c`. -/
@[simp]
theorem face_zero_one_sweep {m : ℕ} (c : SingularCube X m) :
    SingularCube.face 0 1 (D.sweep c) = D.endCube c := by
  simp [sweep]

/-- The faces of the swept cube in the spatial coordinates are the swept faces. -/
@[simp]
theorem face_succ_sweep {m : ℕ} (c : SingularCube X (m + 1)) (i : Fin (m + 1)) {t : I}
    (ht : t = 0 ∨ t = 1) :
    SingularCube.face i.succ t (D.sweep c) = D.sweep (SingularCube.face i t c) := by
  ext y
  rw [SingularCube.face_apply, sweep_apply, sweep_apply, ← Fin.cons_self_tail y,
    Fin.insertNth_succ_cons]
  simp [D.homotopy_insertNth c i ht]

/-- If `c` does not depend on its coordinate `i`, then its swept cube does not depend on the
coordinate `i.succ`. -/
theorem isDegenerateAt_sweep {m : ℕ} {c : SingularCube X m} {i : Fin m}
    (hc : c.IsDegenerateAt i) : (D.sweep c).IsDegenerateAt i.succ := by
  rw [SingularCube.isDegenerateAt_iff]
  intro y t
  have h := SingularCube.isDegenerateAt_iff.1 (D.isDegenerateAt_curry hc (y 0)) (Fin.tail y) t
  simpa [Fin.tail_update_succ, Function.update_of_ne (Fin.succ_ne_zero i).symm] using h

/-- The cube swept out by the deformation of a degenerate cube is degenerate. -/
theorem isDegenerate_sweep {m : ℕ} {c : SingularCube X m} (hc : c.IsDegenerate) :
    (D.sweep c).IsDegenerate :=
  (SingularCube.isDegenerate_iff.1 hc).elim fun _ hi ↦ (D.isDegenerateAt_sweep hi).isDegenerate

/-! ### The operators on normalized chains -/

variable (R : Type*) [Ring R]

/-- The end of the deformation, on normalized cubical chains of `X`. -/
def endChain (m : ℕ) : NormalizedCubicalChain X R m →ₗ[R] NormalizedCubicalChain X R m :=
  Submodule.mapQ _ _ (lmapDomain R R D.endCube) fun _ hg ↦
    CubicalChain.lmapDomain_mem_degenerate R (fun _ ↦ D.isDegenerate_endCube) hg

/-- The negative swept-cube operator on normalized cubical chains. -/
def prismChain (m : ℕ) : NormalizedCubicalChain X R m →ₗ[R] NormalizedCubicalChain X R (m + 1) :=
  -Submodule.mapQ _ _ (lmapDomain R R D.sweep) fun _ hg ↦
    CubicalChain.lmapDomain_mem_degenerate R (fun _ ↦ D.isDegenerate_sweep) hg

@[simp]
theorem endChain_ofCube {m : ℕ} (c : SingularCube X m) :
    D.endChain R m (NormalizedCubicalChain.ofCube X R c) =
      NormalizedCubicalChain.ofCube X R (D.endCube c) := by
  simp [endChain, NormalizedCubicalChain.ofCube_def, lmapDomain_apply]

@[simp]
theorem prismChain_ofCube {m : ℕ} (c : SingularCube X m) :
    D.prismChain R m (NormalizedCubicalChain.ofCube X R c) =
      -NormalizedCubicalChain.ofCube X R (D.sweep c) := by
  simp [prismChain, NormalizedCubicalChain.ofCube_def, lmapDomain_apply]

/-- The end of the deformation commutes with the boundary. -/
theorem boundary_endChain (m : ℕ) (g : NormalizedCubicalChain X R (m + 1)) :
    NormalizedCubicalChain.boundary X R m (D.endChain R (m + 1) g) =
      D.endChain R m (NormalizedCubicalChain.boundary X R m g) := by
  induction g using NormalizedCubicalChain.induction_on with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | smul r a ha => simp [ha]
  | ofCube c => simp [D.face_endCube c _ (Or.inl rfl), D.face_endCube c _ (Or.inr rfl)]

/-- **The prism identity** `∂ P + P ∂ = ε - id` in positive degrees, for the swept-cube operator
`P` and the end `ε` of the deformation. -/
theorem boundary_prismChain_add_prismChain_boundary (m : ℕ)
    (g : NormalizedCubicalChain X R (m + 1)) :
    NormalizedCubicalChain.boundary X R (m + 1) (D.prismChain R (m + 1) g) +
        D.prismChain R m (NormalizedCubicalChain.boundary X R m g) =
      D.endChain R (m + 1) g - g := by
  induction g using NormalizedCubicalChain.induction_on with
  | zero => simp
  | add a b ha hb =>
    simp only [map_add]
    rw [add_add_add_comm, ha, hb]
    abel
  | smul r a ha => simp only [map_smul, ← smul_add, ha, smul_sub]
  | ofCube c =>
    simp only [prismChain_ofCube, endChain_ofCube, map_neg,
      NormalizedCubicalChain.boundary_ofCube, map_sum, map_smul, map_sub]
    rw [Fin.sum_univ_succ]
    simp only [face_zero_zero_sweep, face_zero_one_sweep, D.face_succ_sweep c _ (Or.inl rfl),
      D.face_succ_sweep c _ (Or.inr rfl), Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ,
      mul_neg_one, neg_smul, smul_neg, smul_sub]
    abel

/-- The prism identity `∂ P = ε - id` in degree zero. -/
theorem boundary_prismChain_zero (g : NormalizedCubicalChain X R 0) :
    NormalizedCubicalChain.boundary X R 0 (D.prismChain R 0 g) = D.endChain R 0 g - g := by
  induction g using NormalizedCubicalChain.induction_on with
  | zero => simp
  | add a b ha hb =>
    simp only [map_add, ha, hb]
    abel
  | smul r a ha => simp [ha, smul_sub]
  | ofCube c => simp

end CubeDeformation

end Cubes

/-! ### The chain homotopy from the identity to the end of the deformation -/

universe u

namespace CubeDeformation

variable {X : TopCat.{u}} (D : CubeDeformation X) (R : Type u) [Ring R]

/-- The end of the deformation, as an endomorphism of the normalized cubical chain complex of
`X`. -/
def endChainMap :
    (normalizedCubicalChainComplex R).obj X ⟶ (normalizedCubicalChainComplex R).obj X :=
  ChainComplex.ofHom (fun m ↦ ModuleCat.ofHom (D.endChain R m)) fun m ↦ by
    ext g
    exact (normalizedCubicalChainComplex_obj_d_apply X m _).trans
      ((D.boundary_endChain R m g).trans
        (congrArg _ (normalizedCubicalChainComplex_obj_d_apply X m g).symm))

@[simp]
theorem endChainMap_f_apply (m : ℕ) (g : NormalizedCubicalChain X R m) :
    (D.endChainMap R).f m g = D.endChain R m g :=
  (rfl)

/-- Under the concrete identification of chain-complex terms, the chain map of the end of the
deformation acts by `TauCeti.CubeDeformation.endChain`. -/
theorem normalizedCubicalChainComplexXEquiv_endChainMap_f_apply (m : ℕ)
    (g : ((normalizedCubicalChainComplex R).obj X).X m) :
    normalizedCubicalChainComplexXEquiv X m ((D.endChainMap R).f m g) =
      D.endChain R m (normalizedCubicalChainComplexXEquiv X m g) :=
  let e := normalizedCubicalChainComplexXEquiv X m
  calc
    e ((D.endChainMap R).f m g) =
        e ((D.endChainMap R).f m (e.symm (e g))) := by rw [e.symm_apply_apply]
    _ = e (D.endChain R m (e g)) :=
      congrArg e (D.endChainMap_f_apply R m (e g))
    _ = D.endChain R m (e g) := normalizedCubicalChainComplexXEquiv_apply X m _

/-- The negative swept-cube operator, as a morphism between the terms of the normalized cubical
chain complex. -/
private def prismHom (m : ℕ) :
    ((normalizedCubicalChainComplex R).obj X).X m ⟶
      ((normalizedCubicalChainComplex R).obj X).X (m + 1) :=
  ModuleCat.ofHom (D.prismChain R m)

/-- **The chain homotopy from the identity to the end of the deformation**, given in degree `m` by
the swept-cube operator `-D.prismChain R m`. -/
def endHomotopy : Homotopy (𝟙 _) (D.endChainMap R) :=
  (Homotopy.equivSubZero.symm
    (Homotopy.mkChainComplex (D.endChainMap R - 𝟙 _)
      (D.prismHom R)
      (by
        ext g
        simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, ModuleCat.hom_sub,
          ModuleCat.hom_id, ModuleCat.hom_comp, LinearMap.sub_apply, LinearMap.id_apply,
          LinearMap.comp_apply]
        exact (D.boundary_prismChain_zero R g).symm)
      (fun m ↦ by
        ext g
        -- The differentials of `ChainComplex.of` are the boundaries only after `ChainComplex.of_d`.
        have h₁ := normalizedCubicalChainComplex_obj_d_apply (R := R) X m g
        have h₂ := normalizedCubicalChainComplex_obj_d_apply (R := R) X (m + 1) (D.prismHom R _ g)
        simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, ModuleCat.hom_sub,
          ModuleCat.hom_id, ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.sub_apply,
          LinearMap.id_apply, LinearMap.add_apply, LinearMap.comp_apply]
        rw [h₁, h₂]
        exact (D.boundary_prismChain_add_prismChain_boundary R m g).symm.trans (add_comm _ _))))
    |>.symm

@[simp]
theorem endHomotopy_hom_succ (m : ℕ) (g : NormalizedCubicalChain X R m) :
    (D.endHomotopy R).hom m (m + 1) g = -D.prismChain R m g := by
  simp only [endHomotopy, Homotopy.symm_hom, Homotopy.equivSubZero, Equiv.coe_fn_symm_mk]
  rw [Homotopy.mkChainComplex_hom_succ]
  -- `prismHom` is `prismChain` viewed as a morphism of modules, so this holds by definition.
  rfl

end CubeDeformation

end TauCeti
