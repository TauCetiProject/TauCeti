/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Homotopy
public import TauCeti.AlgebraicTopology.Singular.Cubical.Based.Deformation
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Basic
public import TauCeti.AlgebraicTopology.Singular.Cubical.Prism

/-!
# The retraction of cubical chains onto based chains

Let `D` be a `TauCeti.BasedCubeDeformation n x`: a homotopy of every singular cube `c` of `X` to
an `n`-based cube, compatible with faces and degeneracies. This file turns `D` into chain-level
data on Massey's normalized cubical chains.

* The end of the homotopy of `c` is the `n`-based cube `D.retract c`. It commutes with faces and
  preserves degeneracies, so it induces a chain map `D.retractChainMap R` of normalized cubical
  chains, whose image is spanned by `n`-based cubes.
* The homotopy of `c`, with time as the first coordinate, sweeps out the cube `D.sweep c` of one
  dimension more. Its first two faces are `c` and `D.retract c`, and its other faces are the swept
  faces of `c`. The negative swept-cube operator `D.prismChain R` therefore satisfies
  `∂ P + P ∂ = ρ - id`, so the swept-cube operator `-D.prismChain R` is a chain homotopy
  `D.retractHomotopy R` from the identity to `D.retractChainMap R`.

In a dimension `m` with `0 < m < n`, the only `n`-based `m`-cube is the constant cube at `x`, which
is degenerate, so the retraction vanishes. As it induces the identity on homology, the normalized
cubical homology of `X` vanishes in these degrees. By the comparison of cubical and simplicial
singular chains, so does the singular homology of `X`: **the singular homology of an
`(n - 1)`-connected space vanishes in the positive degrees below `n`**
(`TauCeti.isZero_singularHomologyFunctor_of_subsingleton_homotopyGroup`).

In degree `n` the retraction lands in the span of the `n`-based `n`-cubes, which are the
generalized loops of `Ω^ (Fin n) X x`; this is where the identification of the `n`-th homology with
the homotopy group through the Hurewicz map starts.

## Main definitions

* `TauCeti.BasedCubeDeformation.retract`, `TauCeti.BasedCubeDeformation.cubeHomotopy`,
  `TauCeti.BasedCubeDeformation.sweep`: the end of the deformation of a cube, the deformation as a
  homotopy, and the cube it sweeps out (its `SingularCube.prism`).
* `TauCeti.BasedCubeDeformation.retractChain`, `TauCeti.BasedCubeDeformation.prismChain`: the
  induced operators on normalized cubical chains.
* `TauCeti.BasedCubeDeformation.retractChainMap`, `TauCeti.BasedCubeDeformation.retractHomotopy`:
  the retraction as an endomorphism of the normalized cubical chain complex, and the chain
  homotopy from the identity to it.

## Main results

* `TauCeti.BasedCubeDeformation.boundary_prismChain_add_prismChain_boundary`: the prism identity
  `∂ P + P ∂ = ρ - id`.
* `TauCeti.BasedCubeDeformation.retractChain_eq_zero`: the retraction vanishes in the positive
  dimensions below `n`.
* `TauCeti.isZero_homology_normalizedCubicalChainComplex_of_subsingleton_homotopyGroup`,
  `TauCeti.isZero_singularHomologyFunctor_of_subsingleton_homotopyGroup`: the vanishing of the
  normalized cubical and of the singular homology of an `(n - 1)`-connected space in the positive
  degrees below `n`.

## References

* S. Eilenberg, *Singular homology theory*, Ann. of Math. (2) 45 (1944), 407–447, for the
  deformation of singular chains of an `(n - 1)`-connected space into the subcomplex of simplices
  sending the `(n - 1)`-skeleton to the base point.
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter II, for normalized
  cubical chains and their prism operators.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology unitInterval Finsupp

namespace TauCeti

section Cubes

variable {X : Type*} [TopologicalSpace X] {n : ℕ} {x : X}

namespace BasedCubeDeformation

variable (D : BasedCubeDeformation n x)

/-! ### The end of the deformation and the swept cube -/

/-- The `n`-based cube at the end of the deformation of the singular cube `c`. -/
def retract {m : ℕ} (c : SingularCube X m) : SingularCube X m :=
  (D.homotopy c).curry 1

@[simp]
theorem retract_apply {m : ℕ} (c : SingularCube X m) (y : Fin m → I) :
    D.retract c y = D.homotopy c (1, y) :=
  (rfl)

/-- The deformation of every cube ends at an `n`-based cube. -/
theorem isBased_retract {m : ℕ} (c : SingularCube X m) : (D.retract c).IsBased n x :=
  D.isBased_curry_one c

/-- The deformation fixes the `n`-based cubes. -/
theorem retract_of_isBased {m : ℕ} {c : SingularCube X m} (hc : c.IsBased n x) :
    D.retract c = c := by
  ext y
  simp [hc]

/-- The end of the deformation commutes with the faces at the endpoints of the interval. -/
theorem face_retract {m : ℕ} (c : SingularCube X (m + 1)) (i : Fin (m + 1)) {t : I}
    (ht : t = 0 ∨ t = 1) :
    SingularCube.face i t (D.retract c) = D.retract (SingularCube.face i t c) := by
  ext y
  simp [D.homotopy_insertNth c i ht]

/-- If `c` does not depend on its coordinate `i`, then neither does the end of its
deformation. -/
theorem isDegenerateAt_retract {m : ℕ} {c : SingularCube X m} {i : Fin m}
    (hc : c.IsDegenerateAt i) : (D.retract c).IsDegenerateAt i :=
  D.isDegenerateAt_curry hc 1

/-- The end of the deformation of a degenerate cube is degenerate. -/
theorem isDegenerate_retract {m : ℕ} {c : SingularCube X m} (hc : c.IsDegenerate) :
    (D.retract c).IsDegenerate :=
  (SingularCube.isDegenerate_iff.1 hc).elim fun _ hi ↦ (D.isDegenerateAt_retract hi).isDegenerate

/-- In a dimension below `n`, every cube retracts to the constant cube at `x`. -/
theorem retract_eq_const {m : ℕ} (hm : m < n) (c : SingularCube X m) :
    D.retract c = ContinuousMap.const _ x := by
  ext y
  exact (SingularCube.isBased_iff_of_lt hm).1 (D.isBased_retract c) y

/-- The deformation of the singular cube `c`, as a homotopy from `c` to `D.retract c`. -/
def cubeHomotopy {m : ℕ} (c : SingularCube X m) : ContinuousMap.Homotopy c (D.retract c) where
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

/-- The swept cube starts at `c`. -/
@[simp]
theorem face_zero_zero_sweep {m : ℕ} (c : SingularCube X m) :
    SingularCube.face 0 0 (D.sweep c) = c := by
  simp [sweep]

/-- The swept cube ends at the retraction of `c`. -/
@[simp]
theorem face_zero_one_sweep {m : ℕ} (c : SingularCube X m) :
    SingularCube.face 0 1 (D.sweep c) = D.retract c := by
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

/-- The retraction onto `n`-based cubes, on normalized cubical chains. -/
def retractChain (m : ℕ) : NormalizedCubicalChain X R m →ₗ[R] NormalizedCubicalChain X R m :=
  Submodule.mapQ _ _ (lmapDomain R R D.retract) fun _ hg ↦
    CubicalChain.lmapDomain_mem_degenerate R (fun _ ↦ D.isDegenerate_retract) hg

/-- The negative swept-cube operator on normalized cubical chains. -/
def prismChain (m : ℕ) : NormalizedCubicalChain X R m →ₗ[R] NormalizedCubicalChain X R (m + 1) :=
  -Submodule.mapQ _ _ (lmapDomain R R D.sweep) fun _ hg ↦
    CubicalChain.lmapDomain_mem_degenerate R (fun _ ↦ D.isDegenerate_sweep) hg

@[simp]
theorem retractChain_ofCube {m : ℕ} (c : SingularCube X m) :
    D.retractChain R m (NormalizedCubicalChain.ofCube X R c) =
      NormalizedCubicalChain.ofCube X R (D.retract c) := by
  simp [retractChain, NormalizedCubicalChain.ofCube_def, lmapDomain_apply]

@[simp]
theorem prismChain_ofCube {m : ℕ} (c : SingularCube X m) :
    D.prismChain R m (NormalizedCubicalChain.ofCube X R c) =
      -NormalizedCubicalChain.ofCube X R (D.sweep c) := by
  simp [prismChain, NormalizedCubicalChain.ofCube_def, lmapDomain_apply]

/-- The retraction lands in the span of the `n`-based cubes. -/
theorem retractChain_mem_span {m : ℕ} (g : NormalizedCubicalChain X R m) :
    D.retractChain R m g ∈ Submodule.span R
      (NormalizedCubicalChain.ofCube X R '' {c | c.IsBased n x}) := by
  induction g using NormalizedCubicalChain.induction_on with
  | zero => simp
  | add a b ha hb => simpa using Submodule.add_mem _ ha hb
  | smul r a ha => simpa using Submodule.smul_mem _ r ha
  | ofCube c =>
    rw [retractChain_ofCube]
    exact Submodule.subset_span ⟨_, D.isBased_retract c, rfl⟩

/-- **The retraction vanishes in the positive dimensions below `n`**: there, every cube retracts
to the constant cube at `x`, which is degenerate. -/
theorem retractChain_eq_zero {m : ℕ} (hm : m + 1 < n) : D.retractChain R (m + 1) = 0 := by
  refine NormalizedCubicalChain.linearMap_ext fun c ↦ ?_
  rw [retractChain_ofCube, D.retract_eq_const hm, LinearMap.zero_apply]
  exact NormalizedCubicalChain.ofCube_eq_zero R
    (SingularCube.isDegenerate_iff.2 ⟨0, SingularCube.isDegenerateAt_iff.2 fun _ _ ↦ rfl⟩)

/-- The retraction commutes with the boundary. -/
theorem boundary_retractChain (m : ℕ) (g : NormalizedCubicalChain X R (m + 1)) :
    NormalizedCubicalChain.boundary X R m (D.retractChain R (m + 1) g) =
      D.retractChain R m (NormalizedCubicalChain.boundary X R m g) := by
  induction g using NormalizedCubicalChain.induction_on with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | smul r a ha => simp [ha]
  | ofCube c => simp [D.face_retract c _ (Or.inl rfl), D.face_retract c _ (Or.inr rfl)]

/-- **The prism identity** `∂ P + P ∂ = ρ - id` in positive degrees, for the swept-cube operator
`P` and the retraction `ρ`. -/
theorem boundary_prismChain_add_prismChain_boundary (m : ℕ)
    (g : NormalizedCubicalChain X R (m + 1)) :
    NormalizedCubicalChain.boundary X R (m + 1) (D.prismChain R (m + 1) g) +
        D.prismChain R m (NormalizedCubicalChain.boundary X R m g) =
      D.retractChain R (m + 1) g - g := by
  induction g using NormalizedCubicalChain.induction_on with
  | zero => simp
  | add a b ha hb =>
    simp only [map_add]
    rw [add_add_add_comm, ha, hb]
    abel
  | smul r a ha => simp only [map_smul, ← smul_add, ha, smul_sub]
  | ofCube c =>
    simp only [prismChain_ofCube, retractChain_ofCube, map_neg,
      NormalizedCubicalChain.boundary_ofCube, map_sum, map_smul, map_sub]
    rw [Fin.sum_univ_succ]
    simp only [face_zero_zero_sweep, face_zero_one_sweep, D.face_succ_sweep c _ (Or.inl rfl),
      D.face_succ_sweep c _ (Or.inr rfl), Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ,
      mul_neg_one, neg_smul, smul_neg, smul_sub]
    abel

/-- The prism identity `∂ P = ρ - id` in degree zero. -/
theorem boundary_prismChain_zero (g : NormalizedCubicalChain X R 0) :
    NormalizedCubicalChain.boundary X R 0 (D.prismChain R 0 g) = D.retractChain R 0 g - g := by
  induction g using NormalizedCubicalChain.induction_on with
  | zero => simp
  | add a b ha hb =>
    simp only [map_add, ha, hb]
    abel
  | smul r a ha => simp [ha, smul_sub]
  | ofCube c => simp

end BasedCubeDeformation

end Cubes

/-! ### The chain homotopy on the normalized cubical chain complex -/

universe u

namespace BasedCubeDeformation

variable {X : TopCat.{u}} {n : ℕ} {x : X} (D : BasedCubeDeformation n x) (R : Type u) [Ring R]

/-- The retraction onto `n`-based cubes, as an endomorphism of the normalized cubical chain
complex. -/
def retractChainMap :
    (normalizedCubicalChainComplex R).obj X ⟶ (normalizedCubicalChainComplex R).obj X :=
  ChainComplex.ofHom (fun m ↦ ModuleCat.ofHom (D.retractChain R m)) fun m ↦ by
    ext g
    exact (normalizedCubicalChainComplex_obj_d_apply X m _).trans
      ((D.boundary_retractChain R m g).trans
        (congrArg _ (normalizedCubicalChainComplex_obj_d_apply X m g).symm))

@[simp]
theorem retractChainMap_f_apply (m : ℕ) (g : NormalizedCubicalChain X R m) :
    (D.retractChainMap R).f m g = D.retractChain R m g :=
  (rfl)

/-- The negative swept-cube operator, as a morphism between the terms of the normalized cubical
chain complex. -/
private def prismHom (m : ℕ) :
    ((normalizedCubicalChainComplex R).obj X).X m ⟶
      ((normalizedCubicalChainComplex R).obj X).X (m + 1) :=
  ModuleCat.ofHom (D.prismChain R m)

/-- **The chain homotopy from the identity to the retraction onto `n`-based cubes**, given in
degree `m` by the swept-cube operator `-D.prismChain R m`. -/
def retractHomotopy : Homotopy (𝟙 _) (D.retractChainMap R) :=
  (Homotopy.equivSubZero.symm
    (Homotopy.mkChainComplex (D.retractChainMap R - 𝟙 _)
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
theorem retractHomotopy_hom_succ (m : ℕ) (g : NormalizedCubicalChain X R m) :
    (D.retractHomotopy R).hom m (m + 1) g = -D.prismChain R m g := by
  simp only [retractHomotopy, Homotopy.symm_hom, Homotopy.equivSubZero, Equiv.coe_fn_symm_mk]
  rw [Homotopy.mkChainComplex_hom_succ]
  -- `prismHom` is `prismChain` viewed as a morphism of modules, so this holds by definition.
  rfl

end BasedCubeDeformation

/-- **The normalized cubical homology of an `(n - 1)`-connected space vanishes in the positive
degrees below `n`.** The retraction onto `n`-based cubes induces the identity on homology, since it
is chain homotopic to the identity, and it vanishes in these degrees. -/
theorem isZero_homology_normalizedCubicalChainComplex_of_subsingleton_homotopyGroup
    {X : TopCat.{u}} {n : ℕ} {x : X} (hX : ∀ k < n, Subsingleton (HomotopyGroup (Fin k) X x))
    (R : Type u) [Ring R] {m : ℕ} (hm0 : m ≠ 0) (hm : m < n) :
    IsZero (((normalizedCubicalChainComplex R).obj X).homology m) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  set D := basedCubeDeformation hX
  have hρ : (D.retractChainMap R).f (m + 1) = 0 := by
    ext g
    exact LinearMap.congr_fun (D.retractChain_eq_zero R hm) g
  have hcycles : HomologicalComplex.cyclesMap (D.retractChainMap R) (m + 1) = 0 := by
    rw [← cancel_mono (HomologicalComplex.iCycles _ (m + 1)), HomologicalComplex.cyclesMap_i,
      hρ, comp_zero, zero_comp]
  rw [IsZero.iff_id_eq_zero, ← HomologicalComplex.homologyMap_id,
    (D.retractHomotopy R).homologyMap_eq, ← cancel_epi (HomologicalComplex.homologyπ _ (m + 1)),
    HomologicalComplex.homologyπ_naturality, hcycles, zero_comp, comp_zero]

/-- **The singular homology of an `(n - 1)`-connected space vanishes in the positive degrees below
`n`.** If `π_k(X, x)` is trivial for every `k < n` (for `k = 0`, if `X` is path connected), then
`H_m(X; R) = 0` for `0 < m < n`, for every coefficient ring `R`. -/
theorem isZero_singularHomologyFunctor_of_subsingleton_homotopyGroup {X : TopCat.{u}} {n : ℕ}
    {x : X} (hX : ∀ k < n, Subsingleton (HomotopyGroup (Fin k) X x)) (R : Type u) [Ring R]
    {m : ℕ} (hm0 : m ≠ 0) (hm : m < n) :
    IsZero (((singularHomologyFunctor (ModuleCat.{u} R) m).obj (ModuleCat.of R R)).obj X) :=
  (isZero_homology_normalizedCubicalChainComplex_of_subsingleton_homotopyGroup hX R hm0
    hm).of_iso (singularCubicalHomologyIso R X m)

end TauCeti
