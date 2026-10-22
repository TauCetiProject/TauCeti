/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Homotopy
public import TauCeti.AlgebraicTopology.Singular.Cubical.Compression.Deformation
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Basic
public import TauCeti.AlgebraicTopology.Singular.Cubical.Prism

/-!
# The retraction of cubical chains onto the chains of a compressible subspace

Let `D` be a `TauCeti.SubspaceCubeDeformation A n`: a homotopy of every singular cube `c` of `X`,
ending at a cube with values in `A ⊆ X` when the dimension of `c` is less than `n`, compatible with
faces and degeneracies and constant on the cubes that already have values in `A`. This file turns
`D` into chain-level data on Massey's normalized cubical chains and shows that, for `n = ⊤`, **the
inclusion `A → X` induces a chain homotopy equivalence of normalized cubical chains**.

* The end of the homotopy of `c` is a cube `D.endCube c` of `X`. It commutes with faces and
  preserves degeneracies, so it induces a chain endomorphism `D.endChainMap R` of the normalized
  cubical chains of `X`. It fixes the chains pushed forward into `A`, and below dimension `n` it
  carries every chain into them.
* The homotopy of `c`, with time as the first coordinate, sweeps out the cube `D.sweep c` of one
  dimension more. Its first two faces are `c` and `D.endCube c`, and its other faces are the swept
  faces of `c`. The negative swept-cube operator `D.prismChain R` therefore satisfies
  `∂ P + P ∂ = ε - id` for the end `ε` of the deformation, so the swept-cube operator
  `-D.prismChain R` is a chain homotopy `D.endHomotopy R` from the identity to `D.endChainMap R`.
  It kills the chains of `A`, whose deformations are constant.
* For `n = ⊤`, the end of the homotopy of `c` is a cube `D.retract c` of `A`, which induces a chain
  map `D.retractChainMap R` from the normalized cubical chains of `X` to those of `A`. As the
  homotopy of a cube of `A` is constant, this chain map is a left inverse of the chain map induced
  by the inclusion, on the nose, and its composite with the inclusion is `D.endChainMap R`.

Through the comparison of cubical and simplicial singular chains, for `n = ⊤` the inclusion of `A`
then induces isomorphisms on singular homology with coefficients in any ring
(`TauCeti.SubspaceCubeDeformation.isIso_singularHomologyMap`). By the compression lemma this
applies as soon as every point of `X` is joined by a path to `A` and all relative homotopy sets
`π_{k+1}(X, A, a)` vanish
(`TauCeti.isIso_singularHomologyMap_subtypeVal_of_relHomotopyGroup`). For the inclusion of the
bottom of the mapping cylinder of a weak homotopy equivalence, this gives the invariance of
singular homology under weak homotopy equivalences (Hatcher, Proposition 4.21), proved as
`ContinuousMap.IsWeakHomotopyEquivalence.isIso_singularHomologyMap`.

## Main definitions

* `TauCeti.SubspaceCubeDeformation.endCube`, `TauCeti.SubspaceCubeDeformation.cubeHomotopy`,
  `TauCeti.SubspaceCubeDeformation.sweep`: the end of the deformation of a cube, the deformation
  as a homotopy, and the cube it sweeps out (its `SingularCube.prism`).
* `TauCeti.SubspaceCubeDeformation.endChain`, `TauCeti.SubspaceCubeDeformation.prismChain`: the
  induced operators on normalized cubical chains.
* `TauCeti.SubspaceCubeDeformation.endChainMap`, `TauCeti.SubspaceCubeDeformation.endHomotopy`:
  the end of the deformation as an endomorphism of the normalized cubical chain complex, and the
  chain homotopy from the identity to it.
* `TauCeti.SubspaceCubeDeformation.retract`, `TauCeti.SubspaceCubeDeformation.retractChain`: for
  `n = ⊤`, the end of the deformation as a cube of `A`, and the induced operator on chains.
* `TauCeti.SubspaceCubeDeformation.retractChainMap`,
  `TauCeti.SubspaceCubeDeformation.retractHomotopy`: the retraction as a chain map onto the
  normalized cubical chains of `A`, and the chain homotopy from the identity to its composite with
  the inclusion.
* `TauCeti.SubspaceCubeDeformation.normalizedCubicalChainComplexHomotopyEquiv`: the chain homotopy
  equivalence between the normalized cubical chains of `A` and of `X` induced by the inclusion.

## Main results

* `TauCeti.SubspaceCubeDeformation.boundary_prismChain_add_prismChain_boundary`: the prism identity
  `∂ P + P ∂ = ε - id`.
* `TauCeti.SubspaceCubeDeformation.endChain_map`, `TauCeti.SubspaceCubeDeformation.prismChain_map`,
  `TauCeti.SubspaceCubeDeformation.endChain_mem_range_map`: for a deformation into the range of a
  map `f`, the end of the deformation fixes the chains pushed forward along `f` and the swept-cube
  operator kills them; below dimension `n`, the end of the deformation lands in them.
* `TauCeti.SubspaceCubeDeformation.retractChain_map_subtypeVal`: the retraction is a left inverse
  of the inclusion.
* `TauCeti.SubspaceCubeDeformation.quasiIso_normalizedCubicalChainComplex_map`,
  `TauCeti.SubspaceCubeDeformation.isIso_singularHomologyMap`: the inclusion of `A` induces a
  quasi-isomorphism of normalized cubical chains and isomorphisms on singular homology.
* `TauCeti.isIso_singularHomologyMap_subtypeVal_of_relHomotopyGroup`: the same conclusion from the
  vanishing of the relative homotopy sets.

## References

* The chain-level construction follows the parallel formalization in
  `TauCeti.AlgebraicTopology.Singular.Cubical.Based.Retraction`, adapted so that, for `n = ⊤`, the
  retraction lands in the chains of the subspace.
* S. Eilenberg, *Singular homology theory*, Ann. of Math. (2) 45 (1944), 407–447, for the
  deformation of singular chains into the subcomplex of a subspace.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, Proposition 4.21 (a weak homotopy equivalence induces isomorphisms on homology).
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter II, for normalized
  cubical chains and their prism operators.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology unitInterval Finsupp Set

namespace TauCeti

section Cubes

variable {X : Type*} [TopologicalSpace X] {A : Set X} {n : ℕ∞}

namespace SubspaceCubeDeformation

variable (D : SubspaceCubeDeformation A n)

/-! ### The end of the deformation and the swept cube -/

/-- The cube of `X` at the end of the deformation of the singular cube `c`. -/
def endCube {m : ℕ} (c : SingularCube X m) : SingularCube X m :=
  (D.homotopy c).curry 1

@[simp]
theorem endCube_apply {m : ℕ} (c : SingularCube X m) (y : Fin m → I) :
    D.endCube c y = D.homotopy c (1, y) :=
  (rfl)

/-- A cube with values in `A` is fixed by the deformation. -/
theorem endCube_of_range_subset {m : ℕ} {c : SingularCube X m} (hc : range c ⊆ A) :
    D.endCube c = c := by
  ext y
  simp [D.homotopy_of_range_subset hc]

/-- The deformation of a cube of dimension less than `n` ends in `A`. -/
theorem range_endCube_subset {m : ℕ} (hm : (m : ℕ∞) < n) (c : SingularCube X m) :
    range (D.endCube c) ⊆ A := by
  rintro _ ⟨y, rfl⟩
  exact D.homotopy_one_mem hm c y

/-- The deformation of a cube whose faces have dimension less than `n` ends in a cube sending the
boundary of the cube into `A`. -/
theorem mapsTo_endCube_boundary {m : ℕ} (hm : (m : ℕ∞) < n) (c : SingularCube X (m + 1)) :
    MapsTo (D.endCube c) (Cube.boundary (Fin (m + 1))) A := by
  rintro y ⟨i, hi⟩
  rw [endCube_apply, ← Fin.insertNth_self_removeNth i y, D.homotopy_insertNth c i hi]
  exact D.homotopy_one_mem hm _ _

/-- The end of the deformation commutes with the faces at the endpoints of the interval. -/
theorem face_endCube {m : ℕ} (c : SingularCube X (m + 1)) (i : Fin (m + 1)) {t : I}
    (ht : t = 0 ∨ t = 1) :
    SingularCube.face i t (D.endCube c) = D.endCube (SingularCube.face i t c) := by
  ext y
  simp [D.homotopy_insertNth c i ht]

/-- The end of the deformation of a degenerate cube is degenerate. -/
theorem isDegenerate_endCube {m : ℕ} {c : SingularCube X m} (hc : c.IsDegenerate) :
    (D.endCube c).IsDegenerate :=
  (SingularCube.isDegenerate_iff.1 hc).elim fun _ hi ↦ (D.isDegenerateAt_curry hi 1).isDegenerate

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

/-- The cube swept out by the constant deformation of a cube with values in `A` does not depend on
the time coordinate. -/
theorem isDegenerate_sweep_of_range_subset {m : ℕ} {c : SingularCube X m} (hc : range c ⊆ A) :
    (D.sweep c).IsDegenerate :=
  SingularCube.isDegenerate_iff.2 ⟨0, SingularCube.isDegenerateAt_iff.2 fun y t ↦ by
    simp [D.homotopy_of_range_subset hc]⟩

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

/-! ### Chains pushed forward into the subspace -/

section Map

variable {Y : Type*} [TopologicalSpace Y] {f : C(Y, X)} (D : SubspaceCubeDeformation (range f) n)

/-- The end of a deformation into the range of `f` fixes the chains pushed forward along `f`. -/
@[simp]
theorem endChain_map {m : ℕ} (g : NormalizedCubicalChain Y R m) :
    D.endChain R m (NormalizedCubicalChain.map R f m g) = NormalizedCubicalChain.map R f m g := by
  induction g using NormalizedCubicalChain.induction_on with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | smul r a ha => simp [ha]
  | ofCube c =>
    rw [NormalizedCubicalChain.map_ofCube, endChain_ofCube, D.endCube_of_range_subset]
    rintro _ ⟨y, rfl⟩
    exact ⟨c y, rfl⟩

/-- The swept-cube operator of a deformation into the range of `f` kills the chains pushed forward
along `f`, whose deformations are constant. -/
@[simp]
theorem prismChain_map {m : ℕ} (g : NormalizedCubicalChain Y R m) :
    D.prismChain R m (NormalizedCubicalChain.map R f m g) = 0 := by
  induction g using NormalizedCubicalChain.induction_on with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | smul r a ha => simp [ha]
  | ofCube c =>
    rw [NormalizedCubicalChain.map_ofCube, prismChain_ofCube, neg_eq_zero]
    refine NormalizedCubicalChain.ofCube_eq_zero R (D.isDegenerate_sweep_of_range_subset ?_)
    rintro _ ⟨y, rfl⟩
    exact ⟨c y, rfl⟩

/-- **Below dimension `n`, the end of a deformation into the range of an inducing map `f` lands in
the chains pushed forward along `f`.** -/
theorem endChain_mem_range_map (hf : Topology.IsInducing f) {m : ℕ} (hm : (m : ℕ∞) < n)
    (g : NormalizedCubicalChain X R m) :
    D.endChain R m g ∈ LinearMap.range (NormalizedCubicalChain.map R f m) := by
  induction g using NormalizedCubicalChain.induction_on with
  | zero => simp
  | add a b ha hb => simpa using Submodule.add_mem _ ha hb
  | smul r a ha => simpa using Submodule.smul_mem _ r ha
  | ofCube c =>
    rw [endChain_ofCube]
    exact NormalizedCubicalChain.ofCube_mem_range_map R hf (D.range_endCube_subset hm c)

end Map

end SubspaceCubeDeformation

namespace SubspaceCubeDeformation

variable (D : SubspaceCubeDeformation A ⊤)

/-! ### The retraction onto the cubes of `A` -/

/-- The cube of `A` at the end of the deformation of the singular cube `c` of `X`. -/
def retract {m : ℕ} (c : SingularCube X m) : SingularCube A m where
  toFun y := ⟨D.homotopy c (1, y), D.homotopy_one_mem (ENat.natCast_lt_top m) c y⟩
  continuous_toFun := by fun_prop

@[simp]
theorem coe_retract_apply {m : ℕ} (c : SingularCube X m) (y : Fin m → I) :
    (D.retract c y : X) = D.homotopy c (1, y) :=
  (rfl)

/-- Read in `X`, the cube `D.retract c` is the end of the deformation of `c`. -/
@[simp]
theorem subtypeVal_comp_retract {m : ℕ} (c : SingularCube X m) :
    (ContinuousMap.subtypeVal A).comp (D.retract c) = D.endCube c :=
  (rfl)

/-- The deformation fixes the cubes of `A`. -/
@[simp]
theorem retract_subtypeVal_comp {m : ℕ} (c : SingularCube A m) :
    D.retract ((ContinuousMap.subtypeVal A).comp c) = c := by
  have hc : range ((ContinuousMap.subtypeVal A).comp c) ⊆ A := by
    rintro _ ⟨y, rfl⟩
    exact (c y).2
  ext y
  simp [D.homotopy_of_range_subset hc]

/-- The end of the deformation commutes with the faces at the endpoints of the interval. -/
theorem face_retract {m : ℕ} (c : SingularCube X (m + 1)) (i : Fin (m + 1)) {t : I}
    (ht : t = 0 ∨ t = 1) :
    SingularCube.face i t (D.retract c) = D.retract (SingularCube.face i t c) := by
  ext y
  simp [D.homotopy_insertNth c i ht]

/-- If `c` does not depend on its coordinate `i`, then neither does the end of its
deformation. -/
theorem isDegenerateAt_retract {m : ℕ} {c : SingularCube X m} {i : Fin m}
    (hc : c.IsDegenerateAt i) : (D.retract c).IsDegenerateAt i := by
  rw [← SingularCube.isDegenerateAt_comp_iff_of_injective (ContinuousMap.subtypeVal A)
    Subtype.val_injective, subtypeVal_comp_retract]
  exact D.isDegenerateAt_curry hc 1

/-- The end of the deformation of a degenerate cube is degenerate. -/
theorem isDegenerate_retract {m : ℕ} {c : SingularCube X m} (hc : c.IsDegenerate) :
    (D.retract c).IsDegenerate :=
  (SingularCube.isDegenerate_iff.1 hc).elim fun _ hi ↦ (D.isDegenerateAt_retract hi).isDegenerate

variable (R : Type*) [Ring R]

/-- The retraction onto the cubes of `A`, on normalized cubical chains. -/
def retractChain (m : ℕ) : NormalizedCubicalChain X R m →ₗ[R] NormalizedCubicalChain A R m :=
  Submodule.mapQ _ _ (lmapDomain R R D.retract) fun _ hg ↦
    CubicalChain.lmapDomain_mem_degenerate R (fun _ ↦ D.isDegenerate_retract) hg

@[simp]
theorem retractChain_ofCube {m : ℕ} (c : SingularCube X m) :
    D.retractChain R m (NormalizedCubicalChain.ofCube X R c) =
      NormalizedCubicalChain.ofCube A R (D.retract c) := by
  simp [retractChain, NormalizedCubicalChain.ofCube_def, lmapDomain_apply]

/-- **The retraction is a left inverse of the inclusion** on normalized cubical chains, since the
deformation fixes the cubes of `A`. -/
@[simp]
theorem retractChain_map_subtypeVal {m : ℕ} (g : NormalizedCubicalChain A R m) :
    D.retractChain R m (NormalizedCubicalChain.map R (ContinuousMap.subtypeVal A) m g) = g := by
  induction g using NormalizedCubicalChain.induction_on with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | smul r a ha => simp [ha]
  | ofCube c => simp

/-- Read in `X`, the retraction onto the cubes of `A` is the end of the deformation. -/
@[simp]
theorem map_subtypeVal_retractChain {m : ℕ} (g : NormalizedCubicalChain X R m) :
    NormalizedCubicalChain.map R (ContinuousMap.subtypeVal A) m (D.retractChain R m g) =
      D.endChain R m g := by
  induction g using NormalizedCubicalChain.induction_on with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | smul r a ha => simp [ha]
  | ofCube c => simp

/-- The retraction commutes with the boundary. -/
theorem boundary_retractChain (m : ℕ) (g : NormalizedCubicalChain X R (m + 1)) :
    NormalizedCubicalChain.boundary A R m (D.retractChain R (m + 1) g) =
      D.retractChain R m (NormalizedCubicalChain.boundary X R m g) := by
  induction g using NormalizedCubicalChain.induction_on with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | smul r a ha => simp [ha]
  | ofCube c => simp [D.face_retract c _ (Or.inl rfl), D.face_retract c _ (Or.inr rfl)]

end SubspaceCubeDeformation

end Cubes

/-! ### The chain homotopy from the identity to the end of the deformation -/

universe u

namespace SubspaceCubeDeformation

section Homotopy

variable {X : TopCat.{u}} {A : Set X} {n : ℕ∞} (D : SubspaceCubeDeformation A n) (R : Type u)
  [Ring R]

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

end Homotopy

/-! ### The chain homotopy equivalence of normalized cubical chain complexes -/

variable {X : TopCat.{u}} {A : Set X} (D : SubspaceCubeDeformation A ⊤) (R : Type u) [Ring R]

/-- The retraction onto the cubes of `A`, as a chain map from the normalized cubical chains of `X`
to those of `A`. -/
def retractChainMap :
    (normalizedCubicalChainComplex R).obj X ⟶ (normalizedCubicalChainComplex R).obj (TopCat.of A) :=
  ChainComplex.ofHom (fun m ↦ ModuleCat.ofHom (D.retractChain R m)) fun m ↦ by
    ext g
    exact (normalizedCubicalChainComplex_obj_d_apply (TopCat.of A) m _).trans
      ((D.boundary_retractChain R m g).trans
        (congrArg _ (normalizedCubicalChainComplex_obj_d_apply X m g).symm))

@[simp]
theorem retractChainMap_f_apply (m : ℕ) (g : NormalizedCubicalChain X R m) :
    (D.retractChainMap R).f m g = D.retractChain R m g :=
  (rfl)

/-- The retraction chain map is a left inverse of the chain map induced by the inclusion of
`A`. -/
@[reassoc (attr := simp)]
theorem normalizedCubicalChainComplex_map_comp_retractChainMap :
    (normalizedCubicalChainComplex R).map (TopCat.ofHom (ContinuousMap.subtypeVal A)) ≫
      D.retractChainMap R = 𝟙 _ := by
  ext m g
  -- In degree `m` both chain maps act by their concrete linear maps, and the terms of the
  -- normalized cubical chain complex are the modules of normalized chains by definition
  -- (`normalizedCubicalChainComplex_obj_X`), so the goal is the chain-level statement.
  exact D.retractChain_map_subtypeVal R g

/-- Followed by the inclusion of `A`, the retraction chain map is the end of the deformation. -/
@[reassoc (attr := simp)]
theorem retractChainMap_comp_normalizedCubicalChainComplex_map :
    D.retractChainMap R ≫
        (normalizedCubicalChainComplex R).map (TopCat.ofHom (ContinuousMap.subtypeVal A)) =
      D.endChainMap R := by
  ext m g
  exact D.map_subtypeVal_retractChain R g

/-- **The chain homotopy from the identity to the composite of the retraction and the inclusion of
`A`**, given in degree `m` by the swept-cube operator `-D.prismChain R m`. -/
def retractHomotopy :
    Homotopy (𝟙 _) (D.retractChainMap R ≫
      (normalizedCubicalChainComplex R).map (TopCat.ofHom (ContinuousMap.subtypeVal A))) :=
  (D.endHomotopy R).trans
    (Homotopy.ofEq (D.retractChainMap_comp_normalizedCubicalChainComplex_map R).symm)

@[simp]
theorem retractHomotopy_hom_succ (m : ℕ) (g : NormalizedCubicalChain X R m) :
    (D.retractHomotopy R).hom m (m + 1) g = -D.prismChain R m g := by
  simpa [retractHomotopy] using D.endHomotopy_hom_succ R m g

/-- **The inclusion of `A` induces a chain homotopy equivalence of normalized cubical chains**,
with the retraction as homotopy inverse. -/
def normalizedCubicalChainComplexHomotopyEquiv :
    HomotopyEquiv ((normalizedCubicalChainComplex R).obj (TopCat.of A))
      ((normalizedCubicalChainComplex R).obj X) where
  hom := (normalizedCubicalChainComplex R).map (TopCat.ofHom (ContinuousMap.subtypeVal A))
  inv := D.retractChainMap R
  homotopyHomInvId := Homotopy.ofEq (D.normalizedCubicalChainComplex_map_comp_retractChainMap R)
  homotopyInvHomId := (D.retractHomotopy R).symm

@[simp]
theorem normalizedCubicalChainComplexHomotopyEquiv_hom :
    (D.normalizedCubicalChainComplexHomotopyEquiv R).hom =
      (normalizedCubicalChainComplex R).map (TopCat.ofHom (ContinuousMap.subtypeVal A)) :=
  (rfl)

@[simp]
theorem normalizedCubicalChainComplexHomotopyEquiv_inv :
    (D.normalizedCubicalChainComplexHomotopyEquiv R).inv = D.retractChainMap R :=
  (rfl)

/-- **The inclusion of `A` induces a quasi-isomorphism of normalized cubical chains.** -/
theorem quasiIso_normalizedCubicalChainComplex_map (D : SubspaceCubeDeformation A ⊤) :
    QuasiIso ((normalizedCubicalChainComplex R).map (TopCat.ofHom (ContinuousMap.subtypeVal A))) :=
  inferInstanceAs (QuasiIso (D.normalizedCubicalChainComplexHomotopyEquiv R).hom)

/-- **The inclusion of `A` induces isomorphisms on singular homology**, with coefficients in any
ring, when the singular cubes of `X` deform into `A`. -/
theorem isIso_singularHomologyMap (D : SubspaceCubeDeformation A ⊤) (n : ℕ) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).map
      (TopCat.ofHom (ContinuousMap.subtypeVal A))) := by
  have := D.quasiIso_normalizedCubicalChainComplex_map R
  exact TopCat.isIso_singularHomologyMap_of_quasiIso _ n

end SubspaceCubeDeformation

/-- **The inclusion of a subspace with vanishing relative homotopy sets induces isomorphisms on
singular homology.** If every point of `X` is joined by a path to a point of `A`, and the relative
homotopy set `π_{n+1}(X, A, a)` is trivial for every `n` and every `a ∈ A`, then the inclusion of
`A` into `X` induces isomorphisms `H_n(A; R) ≅ H_n(X; R)` for every `n` and every coefficient
ring `R`. -/
theorem isIso_singularHomologyMap_subtypeVal_of_relHomotopyGroup {X : TopCat.{u}} {A : Set X}
    (h₀ : ∀ x : X, ∃ a ∈ A, Joined x a)
    (h : ∀ (n : ℕ) (a : A), Subsingleton (RelHomotopyGroup (Fin n) ⟨TopPair.ofSubset A, a⟩))
    (R : Type u) [Ring R] (n : ℕ) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).map
      (TopCat.ofHom (ContinuousMap.subtypeVal A))) :=
  (nonempty_subspaceCubeDeformation_of_relHomotopyGroup h₀ fun k _ ↦
    h k).some.isIso_singularHomologyMap R n

end TauCeti
