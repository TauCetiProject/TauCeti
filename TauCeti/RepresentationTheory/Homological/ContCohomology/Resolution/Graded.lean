/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.CochainComplex.DirectSum
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CompactDiscrete
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.Contraction
public import TauCeti.RepresentationTheory.Continuous.TopRep.Discrete
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Functoriality

/-!
# The graded module of the coinduced resolution

The shifted canonical resolution has degree-`n` term `C(G, …, C(G, X))`, with `n + 1`
function-space layers. Its external direct sum carries the canonical square-zero differential
of degree one and the componentwise `G`-action. The augmentation includes `X` as constant
functions in degree zero. Coefficient morphisms act degreewise through Mathlib's resolution maps.

For a compact group, a discrete scalar ring `R`, and smooth discrete coefficients, the total
module with its discrete topology is again smooth. This provides a graded coefficient module for
finite tensor induction of resolutions; tensor products can apply the differential on one carrier
while tracking its degree.

Evaluation at `1` contracts the total module onto the coefficients. The projection `π` evaluates
the degree-zero component at `1`, and the homotopy `h`, of degree minus one, is the total map of
the contraction `TopRep.resolutionModuleHomotopy` of the underlying complex. Together with the
augmentation `ι` they satisfy `π ∘ ι = 1` and `d ∘ h + h ∘ d = 1 - ι ∘ π`. Neither `π` nor `h` is
equivariant. Being linear data on one carrier, this contraction can be tensored factor by factor
to contract a tensor power of total resolutions onto the tensor power of the coefficients.

## Main results

* `gradedResolutionTopRepDifferential` bundles the square-zero differential as a morphism of
  discrete topological representations.
* `gradedResolutionTopRepAugmentation` includes discrete coefficients into the degree-zero term
  as a morphism of topological representations, naturally in the coefficients.
* `gradedResolutionTopRepMap` bundles coefficient maps, preserving identities, composition,
  and the differential.
* `TauCeti.smoothGradedResolutionFunctor` packages the smooth total resolution functorially.
* `TauCeti.smoothGradedResolutionAugmentation` is its natural coefficient augmentation, and
  `TauCeti.smoothGradedResolutionDifferential` its differential.
* `gradedResolutionProjection` and `gradedResolutionHomotopy` contract the total resolution:
  `gradedResolutionProjection_augmentation` and
  `gradedResolutionDifferential_gradedResolutionHomotopy_add` are the contraction identities, and
  both maps are natural in the coefficients; `gradedResolutionProjection_eq_zero_of_mem` and
  `gradedResolutionHomotopy_eq_zero_of_mem_zero` say that they vanish in nonzero and in zero
  degree.
* `gradedResolutionModule_add_self_eq_zero`: the total resolution of coefficients that are their
  own additive inverses has the same property.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Transactions of the American Mathematical Society 108 (1963), §§2–5.
* Mathlib's `TopRep.resolution'`, `ContinuousCohomology.resolutionMap`, and
  `Representation.directSum` supply the resolution, coefficient maps, and total action.
-/

public section

open CategoryTheory
open scoped DirectSum

namespace TopRep

universe u v w

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (X : TopRep.{max v w} R G)

private theorem resolutionModuleComplex_lof [DecidableEq ℕ] (n : ℕ) :
    DirectSum.lof R ℕ (fun n ↦ (resolutionModuleComplex X).X n) n =
      DirectSum.lof R ℕ (fun n ↦ (resolutionX X (n + 1)).V) n := rfl

private theorem resolutionModuleComplex_d_apply (n : ℕ)
    (x : (resolutionModuleComplex X).X n) :
    ((resolutionModuleComplex X).d n (n + 1)).hom x = (d X (n + 1)).hom x := by
  simp only [resolutionModuleComplex, CochainComplex.of_d]
  rfl

/-- The direct sum of the shifted coinduced resolution. Degree zero is `C(G, X)`. -/
abbrev gradedResolutionModule := ⨁ n : ℕ, (resolutionX X (n + 1)).V

/-- The canonical differential on the total shifted resolution. -/
noncomputable def gradedResolutionDifferential :
    X.gradedResolutionModule →ₗ[R] X.gradedResolutionModule :=
  (resolutionModuleComplex X).directSumDifferential

/-- On degree `n`, the total differential is the original resolution differential `d (n + 1)`. -/
theorem gradedResolutionDifferential_lof [DecidableEq ℕ] (n : ℕ) (x : (resolutionX X (n + 1)).V) :
    X.gradedResolutionDifferential
        (DirectSum.lof R ℕ (fun n ↦ (resolutionX X (n + 1)).V) n x) =
      DirectSum.lof R ℕ (fun n ↦ (resolutionX X (n + 1)).V) (n + 1)
        ((d X (n + 1)).hom x) := by
  have h := (resolutionModuleComplex X).directSumDifferential_lof n x
  erw [resolutionModuleComplex_lof, resolutionModuleComplex_lof,
    resolutionModuleComplex_d_apply] at h
  exact h

/-- The differential of the total shifted resolution squares to zero. -/
@[simp]
theorem gradedResolutionDifferential_sq (x : X.gradedResolutionModule) :
    X.gradedResolutionDifferential (X.gradedResolutionDifferential x) = 0 :=
  (resolutionModuleComplex X).directSumDifferential_sq x

/-- If every coefficient is its own additive inverse, then so is every element of the total
resolution. -/
theorem gradedResolutionModule_add_self_eq_zero (hX : ∀ x : X.V, x + x = 0)
    (z : X.gradedResolutionModule) : z + z = 0 := by
  induction z using DirectSum.induction_on with
  | zero => exact add_zero 0
  | of n F => rw [← map_add, resolutionX_add_self_eq_zero X hX (n + 1) F, map_zero]
  | add y z hy hz => rw [add_add_add_comm, hy, hz, add_zero]

/-- The integer homogeneous-piece family of the total resolution, zero in negative degrees. -/
noncomputable def gradedResolutionPiece : ℤ → Submodule R X.gradedResolutionModule :=
  (resolutionModuleComplex X).directSumPiece

/-- The homogeneous resolution terms decompose the total resolution as an internal direct sum. -/
theorem isInternal_gradedResolutionPiece : DirectSum.IsInternal X.gradedResolutionPiece :=
  (resolutionModuleComplex X).isInternal_directSumPiece

/-- In a nonnegative degree, the homogeneous piece is the corresponding resolution term's copy. -/
@[simp]
theorem gradedResolutionPiece_natCast [DecidableEq ℕ] (n : ℕ) :
    X.gradedResolutionPiece n =
      LinearMap.range (DirectSum.lof R ℕ (fun n ↦ (resolutionX X (n + 1)).V) n) :=
  (resolutionModuleComplex X).directSumPiece_natCast n

/-- The total resolution has no negative homogeneous pieces. -/
theorem gradedResolutionPiece_of_neg {p : ℤ} (hp : p < 0) :
    X.gradedResolutionPiece p = ⊥ :=
  (resolutionModuleComplex X).directSumPiece_of_neg hp

/-- Inclusion of a resolution term gives an element in its homogeneous degree. -/
theorem lof_mem_gradedResolutionPiece [DecidableEq ℕ] (n : ℕ) (x : (resolutionX X (n + 1)).V) :
    DirectSum.lof R ℕ (fun n ↦ (resolutionX X (n + 1)).V) n x ∈ X.gradedResolutionPiece n :=
  (resolutionModuleComplex X).lof_mem_directSumPiece n x

/-- The total resolution differential has degree one. -/
theorem isHomogeneous_gradedResolutionDifferential :
    TauCeti.LinearMap.IsHomogeneous X.gradedResolutionDifferential X.gradedResolutionPiece
      X.gradedResolutionPiece 1 :=
  (resolutionModuleComplex X).isHomogeneous_directSumDifferential

/-- The componentwise group representation on the total shifted coinduced resolution. -/
noncomputable def gradedResolutionRepresentation : Representation R G X.gradedResolutionModule :=
  Representation.directSum fun n ↦ (resolutionX X (n + 1)).ρ.toRepresentation

/-- The group action on an included term is its original resolution action. -/
theorem gradedResolutionRepresentation_lof [DecidableEq ℕ] (n : ℕ) (g : G)
    (x : (resolutionX X (n + 1)).V) :
    X.gradedResolutionRepresentation g
        (DirectSum.lof R ℕ (fun n ↦ (resolutionX X (n + 1)).V) n x) =
      DirectSum.lof R ℕ (fun n ↦ (resolutionX X (n + 1)).V) n
        ((resolutionX X (n + 1)).ρ g x) := by
  simp [gradedResolutionRepresentation, Representation.directSum,
    ContRepresentation.toMonoidHom_apply]

/-- The degree-`n` component of `g • v` is `g` applied to the degree-`n` component of `v`. -/
@[simp]
theorem component_gradedResolutionRepresentation (n : ℕ) (g : G) (v : X.gradedResolutionModule) :
    DirectSum.component R ℕ (fun n ↦ (resolutionX X (n + 1)).V) n
        (X.gradedResolutionRepresentation g v) =
      (resolutionX X (n + 1)).ρ g
        (DirectSum.component R ℕ (fun n ↦ (resolutionX X (n + 1)).V) n v) := by
  induction v using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    rw [← DirectSum.lof_eq_of R, gradedResolutionRepresentation_lof]
    by_cases h : i = n
    · subst h
      rw [DirectSum.component.lof_self, DirectSum.component.lof_self]
    · rw [DirectSum.component.of, DirectSum.component.of,
        dite_eq_right_iff.2 (fun h' ↦ absurd h' h), dite_eq_right_iff.2 (fun h' ↦ absurd h' h),
        map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- The total resolution differential is equivariant. -/
theorem gradedResolutionDifferential_equivariant (g : G) (x : X.gradedResolutionModule) :
    X.gradedResolutionDifferential (X.gradedResolutionRepresentation g x) =
      X.gradedResolutionRepresentation g (X.gradedResolutionDifferential x) := by
  have h : X.gradedResolutionDifferential.comp (X.gradedResolutionRepresentation g) =
      (X.gradedResolutionRepresentation g).comp X.gradedResolutionDifferential := by
    apply DirectSum.linearMap_ext R
    intro n
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply]
    rw [gradedResolutionRepresentation_lof, gradedResolutionDifferential_lof,
      gradedResolutionDifferential_lof, gradedResolutionRepresentation_lof, hom_comm_apply]
  exact DFunLike.congr_fun h x

/-- The componentwise action preserves the homogeneous pieces. -/
theorem isHomogeneous_gradedResolutionRepresentation (g : G) :
    TauCeti.LinearMap.IsHomogeneous (X.gradedResolutionRepresentation g) X.gradedResolutionPiece
      X.gradedResolutionPiece 0 := by
  rw [TauCeti.LinearMap.isHomogeneous_def]
  intro p x hx
  simp only [add_zero]
  rcases lt_or_ge p 0 with hp | hp
  · rw [X.gradedResolutionPiece_of_neg hp, Submodule.mem_bot] at hx
    simp [hx]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    rw [gradedResolutionPiece_natCast] at hx ⊢
    obtain ⟨y, rfl⟩ := hx
    exact ⟨_, (X.gradedResolutionRepresentation_lof n g y).symm⟩

/-- The augmentation of `X` into the degree-zero term of the total shifted resolution. -/
def gradedResolutionAugmentation : X.V →ₗ[R] X.gradedResolutionModule :=
  (DirectSum.lof R ℕ (fun n ↦ (resolutionX X (n + 1)).V) 0).comp
    (d X 0).hom.toContinuousLinearMap.toLinearMap

/-- The augmentation includes the constant resolution element in degree zero. -/
@[simp]
theorem gradedResolutionAugmentation_apply [h : DecidableEq ℕ] (x : X.V) :
    X.gradedResolutionAugmentation x =
      DirectSum.lof R ℕ (fun n ↦ (resolutionX X (n + 1)).V) 0 ((d X 0).hom x) := by
  cases Subsingleton.elim h Nat.decEq
  rfl

/-- The augmentation takes values in degree zero. -/
theorem gradedResolutionAugmentation_mem (x : X.V) :
    X.gradedResolutionAugmentation x ∈ X.gradedResolutionPiece 0 := by
  simpa only [gradedResolutionAugmentation_apply, Nat.cast_zero] using
    X.lof_mem_gradedResolutionPiece 0 ((d X 0).hom x)

/-- The augmentation takes values in the kernel of the differential. -/
@[simp↓]
theorem gradedResolutionDifferential_augmentation (x : X.V) :
    X.gradedResolutionDifferential (X.gradedResolutionAugmentation x) = 0 := by
  have h := congrArg (fun f ↦ f.hom.toContinuousLinearMap x) (d_comp_d X 0)
  simp only [hom_comp, hom_zero, ContIntertwiningMap.toContinuousLinearMap_comp,
    ContIntertwiningMap.toContinuousLinearMap_zero, ContinuousLinearMap.comp_apply,
    zero_apply, ContIntertwiningMap.toContinuousLinearMap_apply] at h
  rw [gradedResolutionAugmentation_apply, gradedResolutionDifferential_lof, h, map_zero]

/-- The augmentation is equivariant for the original action on `X`. -/
theorem gradedResolutionAugmentation_equivariant (g : G) (x : X.V) :
    X.gradedResolutionAugmentation (X.ρ g x) =
      X.gradedResolutionRepresentation g (X.gradedResolutionAugmentation x) := by
  rw [gradedResolutionAugmentation_apply, gradedResolutionAugmentation_apply,
    gradedResolutionRepresentation_lof, hom_comm_apply]

/-- The augmentation embeds the coefficient module. -/
theorem gradedResolutionAugmentation_injective :
    Function.Injective X.gradedResolutionAugmentation := by
  intro x y h
  rw [gradedResolutionAugmentation_apply, gradedResolutionAugmentation_apply] at h
  have hc := (DirectSum.of_injective _ h)
  have he := congrArg (fun F : (resolutionX X 1).V ↦ F 1) hc
  simpa [d_zero, ContRepresentation.coind₁ι_toFun] using he

section Maps

variable {X} {Y : TopRep.{max v w} R G}

private noncomputable def resolutionModuleMap (f : X ⟶ Y) :
    resolutionModuleComplex X ⟶ resolutionModuleComplex Y :=
  CochainComplex.ofHom (fun n ↦
    let g := _root_.ContinuousCohomology.resolutionMap (ContinuousMonoidHom.id G) f (n + 1)
    ModuleCat.ofHom g.hom.toContinuousLinearMap.toLinearMap) fun n ↦ by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    -- Forgetting to modules preserves the carrier and scalar action definitionally. This
    -- conversion only evaluates the `ofHom` components and composition on that same carrier;
    -- the differential itself is rewritten through its characteristic equation below.
    change ((resolutionModuleComplex Y).d n (n + 1)).hom
        ((_root_.ContinuousCohomology.resolutionMap (ContinuousMonoidHom.id G) f (n + 1)).hom x) =
      (_root_.ContinuousCohomology.resolutionMap (ContinuousMonoidHom.id G) f (n + 1 + 1)).hom
        (((resolutionModuleComplex X).d n (n + 1)).hom x)
    erw [resolutionModuleComplex_d_apply, resolutionModuleComplex_d_apply]
    exact TauCeti.ContinuousCohomology.resolutionMap_d_apply f (n + 1) x

private theorem resolutionModuleMap_f_apply (f : X ⟶ Y) (n : ℕ)
    (x : (resolutionModuleComplex X).X n) :
    ((resolutionModuleMap f).f n).hom x =
      (_root_.ContinuousCohomology.resolutionMap (ContinuousMonoidHom.id G) f (n + 1)).hom x := rfl

/-- The degreewise coefficient map on the total shifted resolution. -/
noncomputable def gradedResolutionMap (f : X ⟶ Y) :
    X.gradedResolutionModule →ₗ[R] Y.gradedResolutionModule :=
  CochainComplex.directSumMap (resolutionModuleMap f)

/-- A coefficient map acts on an included term by Mathlib's canonical resolution map. -/
theorem gradedResolutionMap_lof [DecidableEq ℕ] (f : X ⟶ Y) (n : ℕ)
    (x : (resolutionX X (n + 1)).V) :
    gradedResolutionMap f
      (DirectSum.lof R ℕ (fun n ↦ (resolutionX X (n + 1)).V) n x) =
      DirectSum.lof R ℕ (fun n ↦ (resolutionX Y (n + 1)).V) n
        ((_root_.ContinuousCohomology.resolutionMap (ContinuousMonoidHom.id G)
          f (n + 1)).hom x) := by
  have h := CochainComplex.directSumMap_lof (resolutionModuleMap f) n x
  erw [resolutionModuleComplex_lof, resolutionModuleComplex_lof,
    resolutionModuleMap_f_apply] at h
  exact h

/-- Coefficient maps commute with the total differential. -/
theorem gradedResolutionMap_differential (f : X ⟶ Y) (x : X.gradedResolutionModule) :
    gradedResolutionMap f (X.gradedResolutionDifferential x) =
      Y.gradedResolutionDifferential (gradedResolutionMap f x) :=
  CochainComplex.directSumMap_differential (resolutionModuleMap f) x

/-- Coefficient maps preserve the augmentations of the total resolutions. -/
@[simp↓]
theorem gradedResolutionMap_augmentation (f : X ⟶ Y) (x : X.V) :
    gradedResolutionMap f (X.gradedResolutionAugmentation x) =
      Y.gradedResolutionAugmentation (f.hom x) := by
  rw [gradedResolutionAugmentation_apply, gradedResolutionMap_lof,
    gradedResolutionAugmentation_apply]
  apply congrArg (DirectSum.lof R ℕ (fun n ↦ (resolutionX Y (n + 1)).V) 0)
  have h := (TauCeti.ContinuousCohomology.resolutionMap_d_apply f 0 x).symm
  erw [_root_.ContinuousCohomology.resolutionMap_zero] at h
  exact h

/-- Coefficient maps preserve the homogeneous degrees of the total resolution. -/
theorem isHomogeneous_gradedResolutionMap (f : X ⟶ Y) :
    TauCeti.LinearMap.IsHomogeneous (gradedResolutionMap f) X.gradedResolutionPiece
      Y.gradedResolutionPiece 0 :=
  CochainComplex.isHomogeneous_directSumMap (resolutionModuleMap f)

/-- Coefficient maps on the total resolution are equivariant. -/
theorem gradedResolutionMap_equivariant (f : X ⟶ Y) (g : G) (x : X.gradedResolutionModule) :
    gradedResolutionMap f (X.gradedResolutionRepresentation g x) =
      Y.gradedResolutionRepresentation g (gradedResolutionMap f x) := by
  have h : (gradedResolutionMap f).comp (X.gradedResolutionRepresentation g) =
      (Y.gradedResolutionRepresentation g).comp (gradedResolutionMap f) := by
    apply DirectSum.linearMap_ext R
    intro n
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply]
    rw [gradedResolutionRepresentation_lof, gradedResolutionMap_lof,
      gradedResolutionMap_lof, gradedResolutionRepresentation_lof]
    exact congrArg (DirectSum.lof R ℕ (fun n ↦ (resolutionX Y (n + 1)).V) n)
      (TauCeti.ContinuousCohomology.resolutionMap_ρ_apply f (n + 1) g x)
  exact DFunLike.congr_fun h x

/-- Identity coefficients induce the identity on the total resolution. -/
@[simp]
theorem gradedResolutionMap_id : gradedResolutionMap (𝟙 X) = LinearMap.id := by
  apply DirectSum.linearMap_ext R
  intro n
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  rw [gradedResolutionMap_lof, _root_.ContinuousCohomology.resolutionMap_id]
  rfl

/-- Composite coefficient maps compose on the total resolution. -/
@[simp]
theorem gradedResolutionMap_comp {Z : TopRep.{max v w} R G} (f : X ⟶ Y) (g : Y ⟶ Z) :
    gradedResolutionMap (f ≫ g) = (gradedResolutionMap g).comp (gradedResolutionMap f) := by
  apply DirectSum.linearMap_ext R
  intro n
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  rw [gradedResolutionMap_lof, gradedResolutionMap_lof, gradedResolutionMap_lof]
  have h := congrArg (fun h ↦ h.hom x)
    (_root_.ContinuousCohomology.resolutionMap_comp (ContinuousMonoidHom.id G)
      (ContinuousMonoidHom.id G) f g (n + 1))
  exact congrArg (DirectSum.lof R ℕ (fun n ↦ (resolutionX Z (n + 1)).V) n) h

end Maps

section Contraction

/-- The projection of the total shifted resolution onto its coefficients: evaluation at `1` of
the degree-zero component. It retracts the augmentation, but it is not equivariant. -/
noncomputable def gradedResolutionProjection : X.gradedResolutionModule →ₗ[R] X.V :=
  (ContinuousMap.evalCLM R (1 : G)).toLinearMap ∘ₗ
    DirectSum.component R ℕ (fun n ↦ (resolutionX X (n + 1)).V) 0

/-- The projection evaluates a degree-zero term at `1`. -/
@[simp]
theorem gradedResolutionProjection_lof_zero [h : DecidableEq ℕ] (F : (resolutionX X 1).V) :
    X.gradedResolutionProjection (DirectSum.lof R ℕ (fun n ↦ (resolutionX X (n + 1)).V) 0 F) =
      F 1 := by
  cases Subsingleton.elim h Nat.decEq
  simp [gradedResolutionProjection]

/-- The projection vanishes on the positive-degree terms. -/
@[simp]
theorem gradedResolutionProjection_lof_succ [h : DecidableEq ℕ] (n : ℕ)
    (F : (resolutionX X (n + 1 + 1)).V) :
    X.gradedResolutionProjection
        (DirectSum.lof R ℕ (fun n ↦ (resolutionX X (n + 1)).V) (n + 1) F) = 0 := by
  cases Subsingleton.elim h Nat.decEq
  rw [gradedResolutionProjection, LinearMap.comp_apply, DirectSum.component.of,
    dite_eq_right n.succ_ne_zero, map_zero]

/-- The projection retracts the augmentation. -/
@[simp↓]
theorem gradedResolutionProjection_augmentation (x : X.V) :
    X.gradedResolutionProjection (X.gradedResolutionAugmentation x) = x := by
  classical
  rw [gradedResolutionAugmentation_apply, gradedResolutionProjection_lof_zero]
  simp [d_zero, ContRepresentation.coind₁ι_toFun]

/-- The contracting homotopy of the total shifted resolution: it lowers the degree by one,
evaluating the outermost variable of a positive-degree term at `1`, and vanishes in degree
zero. It is the total map of `TopRep.resolutionModuleHomotopy`, and it is not equivariant. -/
noncomputable def gradedResolutionHomotopy :
    X.gradedResolutionModule →ₗ[R] X.gradedResolutionModule :=
  (resolutionModuleHomotopy X).directSumHomotopy

/-- The contracting homotopy vanishes in degree zero. -/
@[simp]
theorem gradedResolutionHomotopy_lof_zero [DecidableEq ℕ] (F : (resolutionX X 1).V) :
    X.gradedResolutionHomotopy (DirectSum.lof R ℕ (fun n ↦ (resolutionX X (n + 1)).V) 0 F) =
      0 :=
  Homotopy.directSumHomotopy_lof_zero (resolutionModuleHomotopy X) F

/-- In positive degree, the contracting homotopy evaluates the outermost variable at `1`. -/
@[simp]
theorem gradedResolutionHomotopy_lof_succ [DecidableEq ℕ] (n : ℕ)
    (F : (resolutionX X (n + 1 + 1)).V) :
    X.gradedResolutionHomotopy
        (DirectSum.lof R ℕ (fun n ↦ (resolutionX X (n + 1)).V) (n + 1) F) =
      DirectSum.lof R ℕ (fun n ↦ (resolutionX X (n + 1)).V) n (F 1) := by
  rw [gradedResolutionHomotopy, ← resolutionModuleComplex_lof,
    Homotopy.directSumHomotopy_lof_succ, resolutionModuleHomotopy_hom_succ,
    ModuleCat.hom_ofHom, ContinuousLinearMap.coe_coe, ContinuousMap.evalCLM_apply]

/-- The contracting homotopy vanishes on the augmentation. -/
@[simp↓]
theorem gradedResolutionHomotopy_augmentation (x : X.V) :
    X.gradedResolutionHomotopy (X.gradedResolutionAugmentation x) = 0 := by
  classical
  rw [gradedResolutionAugmentation_apply, gradedResolutionHomotopy_lof_zero]

/-- The projection vanishes on the image of the total differential. -/
@[simp]
theorem gradedResolutionProjection_differential (x : X.gradedResolutionModule) :
    X.gradedResolutionProjection (X.gradedResolutionDifferential x) = 0 := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp
  | of n F =>
    rw [← DirectSum.lof_eq_of R, gradedResolutionDifferential_lof,
      gradedResolutionProjection_lof_succ]
  | add x y hx hy => simp [hx, hy]

/-- **The contraction identity** of the total shifted resolution:
`d ∘ h + h ∘ d = 1 - ι ∘ π`, for the augmentation `ι` and the projection `π`. -/
theorem gradedResolutionDifferential_gradedResolutionHomotopy_add (x : X.gradedResolutionModule) :
    X.gradedResolutionDifferential (X.gradedResolutionHomotopy x) +
        X.gradedResolutionHomotopy (X.gradedResolutionDifferential x) =
      x - X.gradedResolutionAugmentation (X.gradedResolutionProjection x) := by
  classical
  have hproj (y : X.gradedResolutionModule) :
      CochainComplex.directSumMap (resolutionModuleProj X ≫ resolutionModuleIncl X) y =
        X.gradedResolutionAugmentation (X.gradedResolutionProjection y) := by
    induction y using DirectSum.induction_on with
    | zero => simp
    | of n F =>
      rw [← DirectSum.lof_eq_of R, ← resolutionModuleComplex_lof,
        CochainComplex.directSumMap_lof, resolutionModuleComplex_lof]
      cases n with
      | zero =>
        rw [gradedResolutionProjection_lof_zero, gradedResolutionAugmentation_apply,
          HomologicalComplex.comp_f, resolutionModuleProj_f_zero, resolutionModuleIncl_f_zero]
        -- The composite of the two `ModuleCat.ofHom` components is evaluation at `1` followed
        -- by the constant-function map; the single complex in degree zero is `X.V` itself.
        rfl
      | succ n =>
        rw [gradedResolutionProjection_lof_succ, map_zero, HomologicalComplex.comp_f,
          resolutionModuleProj_f_succ, Limits.zero_comp, ModuleCat.hom_zero,
          LinearMap.zero_apply, map_zero]
    | add y z hy hz => simp only [map_add, hy, hz]
  have h := Homotopy.directSumDifferential_directSumHomotopy_add
    (resolutionModuleHomotopy X) x
  rwa [CochainComplex.directSumMap_id, LinearMap.id_apply, hproj] at h

/-- The contracting homotopy of the total shifted resolution has degree minus one. -/
theorem isHomogeneous_gradedResolutionHomotopy :
    TauCeti.LinearMap.IsHomogeneous X.gradedResolutionHomotopy X.gradedResolutionPiece
      X.gradedResolutionPiece (-1) :=
  Homotopy.isHomogeneous_directSumHomotopy (resolutionModuleHomotopy X)

/-- The projection vanishes on every homogeneous piece of nonzero degree. -/
theorem gradedResolutionProjection_eq_zero_of_mem {p : ℤ} (hp : p ≠ 0)
    {v : X.gradedResolutionModule} (hv : v ∈ X.gradedResolutionPiece p) :
    X.gradedResolutionProjection v = 0 := by
  classical
  rcases hp.lt_or_gt with hp | hp
  · rw [X.gradedResolutionPiece_of_neg hp, Submodule.mem_bot] at hv
    rw [hv, map_zero]
  · obtain ⟨n, rfl⟩ := Int.eq_succ_of_zero_lt hp
    rw [← Nat.cast_succ, gradedResolutionPiece_natCast] at hv
    obtain ⟨F, rfl⟩ := hv
    exact X.gradedResolutionProjection_lof_succ n F

/-- The contracting homotopy vanishes on the homogeneous piece of degree zero. -/
theorem gradedResolutionHomotopy_eq_zero_of_mem_zero {v : X.gradedResolutionModule}
    (hv : v ∈ X.gradedResolutionPiece 0) : X.gradedResolutionHomotopy v = 0 := by
  classical
  rw [← Nat.cast_zero, gradedResolutionPiece_natCast] at hv
  obtain ⟨F, rfl⟩ := hv
  exact X.gradedResolutionHomotopy_lof_zero F

variable {X} {Y : TopRep.{max v w} R G}

/-- The projection is natural in the coefficients. -/
theorem gradedResolutionProjection_map (f : X ⟶ Y) (x : X.gradedResolutionModule) :
    Y.gradedResolutionProjection (gradedResolutionMap f x) =
      f.hom (X.gradedResolutionProjection x) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp
  | of n F =>
    rw [← DirectSum.lof_eq_of R, gradedResolutionMap_lof]
    cases n with
    | zero =>
      rw [gradedResolutionProjection_lof_zero, gradedResolutionProjection_lof_zero]
      -- At a successor level `resolutionMap` is postcomposition with the previous level by
      -- definition (`ContinuousCohomology.resolutionMap_succ`, `coind₁ResMap_apply`).
      rfl
    | succ n =>
      rw [gradedResolutionProjection_lof_succ, gradedResolutionProjection_lof_succ, map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The contracting homotopy is natural in the coefficients. -/
theorem gradedResolutionHomotopy_map (f : X ⟶ Y) (x : X.gradedResolutionModule) :
    Y.gradedResolutionHomotopy (gradedResolutionMap f x) =
      gradedResolutionMap f (X.gradedResolutionHomotopy x) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp
  | of n F =>
    rw [← DirectSum.lof_eq_of R, gradedResolutionMap_lof]
    cases n with
    | zero => rw [gradedResolutionHomotopy_lof_zero, gradedResolutionHomotopy_lof_zero, map_zero]
    | succ n =>
      rw [gradedResolutionHomotopy_lof_succ, gradedResolutionHomotopy_lof_succ,
        gradedResolutionMap_lof]
      -- At a successor level `resolutionMap` is postcomposition with the previous level by
      -- definition (`ContinuousCohomology.resolutionMap_succ`, `coind₁ResMap_apply`).
      rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end Contraction

section Discrete

variable [DiscreteTopology R]

/-- The total resolution with its discrete topology and componentwise group action. -/
-- The raw-carrier action equations require this carrier identity under module abstraction.
@[expose] noncomputable def gradedResolutionTopRep : TopRep.{max v w} R G :=
  TauCeti.discreteTopRep R G (Rep.of X.gradedResolutionRepresentation)

/-- The bundled discrete representation retains the total resolution carrier. -/
@[simp]
theorem gradedResolutionTopRep_V : X.gradedResolutionTopRep.V = X.gradedResolutionModule :=
  (rfl)

/-- The bundled action is the componentwise resolution action. -/
theorem gradedResolutionTopRep_ρ_apply (g : G) (x : X.gradedResolutionModule) :
    X.gradedResolutionTopRep.ρ g x = X.gradedResolutionRepresentation g x :=
  (rfl)

/-- The bundled discrete action on an included term is the original resolution action. -/
theorem gradedResolutionTopRep_ρ_lof [DecidableEq ℕ] (n : ℕ) (g : G)
    (x : (resolutionX X (n + 1)).V) :
    X.gradedResolutionTopRep.ρ g
      (DirectSum.lof R ℕ (fun n ↦ (resolutionX X (n + 1)).V) n x) =
        DirectSum.lof R ℕ (fun n ↦ (resolutionX X (n + 1)).V) n
          ((resolutionX X (n + 1)).ρ g x) := by
  rw [gradedResolutionTopRep_ρ_apply, gradedResolutionRepresentation_lof]

/-- The bundled discrete action preserves the homogeneous pieces. -/
theorem gradedResolutionTopRep_ρ_mem (n : ℤ) (g : G) (x : X.gradedResolutionModule)
    (hx : x ∈ X.gradedResolutionPiece n) :
    X.gradedResolutionTopRep.ρ g x ∈ X.gradedResolutionPiece n := by
  have h := (X.isHomogeneous_gradedResolutionRepresentation g).map_mem hx
  rw [add_zero] at h
  exact h

/-- The total resolution carries the discrete topology. -/
instance : DiscreteTopology X.gradedResolutionTopRep.V := by
  unfold gradedResolutionTopRep
  infer_instance

/-- The total resolution differential as a morphism of discrete topological representations. -/
noncomputable def gradedResolutionTopRepDifferential :
    X.gradedResolutionTopRep ⟶ X.gradedResolutionTopRep :=
  (TauCeti.discreteTopRepFunctor R G).map <| Rep.ofHom <|
    X.gradedResolutionDifferential.intertwiningMap_of_isIntertwiningMap
      X.gradedResolutionRepresentation X.gradedResolutionRepresentation
      X.gradedResolutionDifferential_equivariant

/-- Bundling the total differential preserves its action on the original direct-sum carrier. -/
theorem gradedResolutionTopRepDifferential_apply (x : X.gradedResolutionModule) :
    X.gradedResolutionTopRepDifferential.hom x = X.gradedResolutionDifferential x :=
  (rfl)

/-- The bundled total differential has degree one. -/
theorem isHomogeneous_gradedResolutionTopRepDifferential :
    TauCeti.LinearMap.IsHomogeneous X.gradedResolutionTopRepDifferential.hom.toLinearMap
      X.gradedResolutionPiece X.gradedResolutionPiece 1 :=
  X.isHomogeneous_gradedResolutionDifferential

/-- The differential of the bundled discrete resolution squares to zero. -/
@[simp]
theorem gradedResolutionTopRepDifferential_sq :
    X.gradedResolutionTopRepDifferential ≫ X.gradedResolutionTopRepDifferential = 0 := by
  ext x
  exact X.gradedResolutionDifferential_sq x

/-- The augmentation from discrete coefficients into the total resolution as a morphism of
topological representations. -/
noncomputable def gradedResolutionTopRepAugmentation [DiscreteTopology X.V] :
    X ⟶ X.gradedResolutionTopRep where
  hom' := {
    toContinuousLinearMap := ⟨X.gradedResolutionAugmentation, continuous_of_discreteTopology⟩
    isIntertwining' g := by
      ext x
      exact X.gradedResolutionAugmentation_equivariant g x
  }

/-- Bundling the augmentation preserves its action on the original coefficient carrier. -/
theorem gradedResolutionTopRepAugmentation_apply [DiscreteTopology X.V] (x : X.V) :
    X.gradedResolutionTopRepAugmentation.hom x = X.gradedResolutionAugmentation x :=
  (rfl)

/-- The bundled augmentation takes values in the kernel of the total differential. -/
theorem gradedResolutionTopRepDifferential_augmentation [DiscreteTopology X.V] :
    X.gradedResolutionTopRepAugmentation ≫ X.gradedResolutionTopRepDifferential = 0 := by
  ext x
  exact X.gradedResolutionDifferential_augmentation x

variable {X} {Y Z : TopRep.{max v w} R G}

/-- A coefficient morphism induces a morphism of discrete total resolutions. -/
noncomputable def gradedResolutionTopRepMap (f : X ⟶ Y) :
    X.gradedResolutionTopRep ⟶ Y.gradedResolutionTopRep :=
  (TauCeti.discreteTopRepFunctor R G).map <| Rep.ofHom <|
    (gradedResolutionMap f).intertwiningMap_of_isIntertwiningMap
      X.gradedResolutionRepresentation Y.gradedResolutionRepresentation
      (gradedResolutionMap_equivariant f)

/-- Bundling a coefficient map preserves its action on the original direct-sum carrier. -/
theorem gradedResolutionTopRepMap_apply (f : X ⟶ Y) (x : X.gradedResolutionModule) :
    (gradedResolutionTopRepMap f).hom x = gradedResolutionMap f x :=
  (rfl)

/-- Identity coefficients induce the identity morphism of the discrete total resolution. -/
@[simp]
theorem gradedResolutionTopRepMap_id : gradedResolutionTopRepMap (𝟙 X) =
    𝟙 X.gradedResolutionTopRep := by
  ext x
  exact DFunLike.congr_fun (gradedResolutionMap_id (X := X)) x

/-- Bundled coefficient maps preserve composition. -/
@[simp]
theorem gradedResolutionTopRepMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    gradedResolutionTopRepMap (f ≫ g) =
      gradedResolutionTopRepMap f ≫ gradedResolutionTopRepMap g := by
  ext x
  exact DFunLike.congr_fun (gradedResolutionMap_comp f g) x

/-- Bundled coefficient maps commute with the resolution differential. -/
theorem gradedResolutionTopRepMap_differential (f : X ⟶ Y) :
    X.gradedResolutionTopRepDifferential ≫ gradedResolutionTopRepMap f =
      gradedResolutionTopRepMap f ≫ Y.gradedResolutionTopRepDifferential := by
  ext x
  exact gradedResolutionMap_differential f x

/-- Bundled coefficient maps preserve the augmentations of discrete coefficients. -/
theorem gradedResolutionTopRepMap_augmentation [DiscreteTopology X.V] [DiscreteTopology Y.V]
    (f : X ⟶ Y) :
    X.gradedResolutionTopRepAugmentation ≫ gradedResolutionTopRepMap f =
      f ≫ Y.gradedResolutionTopRepAugmentation := by
  ext x
  exact gradedResolutionMap_augmentation f x

variable (X)

/-- For a compact group, a discrete scalar ring `R`, and smooth discrete coefficients, the total
coinduced resolution is smooth: each element has finitely many components, whose open
stabilizers have open intersection. -/
theorem isSmoothDiscrete_gradedResolutionTopRep [CompactSpace G]
    (hX : TauCeti.IsSmoothDiscrete R X) :
    TauCeti.IsSmoothDiscrete R X.gradedResolutionTopRep := by
  let : DistribMulAction G X.gradedResolutionModule :=
    X.gradedResolutionTopRep.distribMulAction
  have haction (g : G) (z : X.gradedResolutionModule) :
      g • z = X.gradedResolutionRepresentation g z :=
    (distribMulAction_smul X.gradedResolutionTopRep g z).trans
      (gradedResolutionTopRep_ρ_apply X g z)
  have hstabilizer (z : X.gradedResolutionModule) :
      (MulAction.stabilizer G z : Set G) =
        {g : G | X.gradedResolutionRepresentation g z = z} := by
    ext g
    exact MulAction.mem_stabilizer_iff.trans
      (iff_of_eq (congrArg (fun y ↦ y = z) (haction g z)))
  refine ⟨inferInstance, fun z ↦ ?_⟩
  have hfixed : {g : G | X.gradedResolutionTopRep.ρ g z = z} =
      {g : G | X.gradedResolutionRepresentation g z = z} := by
    ext g
    exact iff_of_eq (congrArg (fun y ↦ y = z) (X.gradedResolutionTopRep_ρ_apply g z))
  rw [hfixed]
  clear hfixed
  induction z using DirectSum.induction_on with
  | zero =>
    simpa only [map_zero, Set.ofPred_true] using (isOpen_univ : IsOpen (Set.univ : Set G))
  | of n x =>
    have h : {g : G | X.gradedResolutionRepresentation g
        (DirectSum.of (fun n ↦ (resolutionX X (n + 1)).V) n x) = DirectSum.of _ n x} =
        {g : G | (resolutionX X (n + 1)).ρ g x = x} := by
      ext g
      simp only [Set.mem_ofPred_eq]
      rw [← DirectSum.lof_eq_of R, gradedResolutionRepresentation_lof]
      exact (DirectSum.of_injective _).eq_iff
    rw [h]
    exact (hX.resolutionX (n + 1)).stabilizer_isOpen x
  | add x y hx hy =>
    rw [← hstabilizer]
    apply Subgroup.isOpen_mono (H₁ := MulAction.stabilizer G x ⊓ MulAction.stabilizer G y)
    · intro g hg
      simp only [Subgroup.mem_inf, MulAction.mem_stabilizer_iff] at hg ⊢
      simp [smul_add, hg.1, hg.2]
    · rw [Subgroup.coe_inf, hstabilizer, hstabilizer]
      exact hx.inter hy

end Discrete

/-- The total differential is nonzero even for trivial-group `𝔽₂` coefficients: the constant
degree-one term with value one has differential equal to the constant degree-two term. -/
example :
    let X := TopRep.of (ContRepresentation.trivial (ZMod 2) PUnit (ZMod 2))
    ∃ z : X.gradedResolutionModule, z ∈ X.gradedResolutionPiece 1 ∧
      X.gradedResolutionDifferential z ≠ 0 := by
  let X := TopRep.of (ContRepresentation.trivial (ZMod 2) PUnit (ZMod 2))
  let F : (resolutionX X 2).V := ContinuousMap.const PUnit
    (ContinuousMap.const PUnit (1 : ZMod 2))
  let z := DirectSum.lof (ZMod 2) ℕ (fun n ↦ (resolutionX X (n + 1)).V) 1 F
  refine ⟨z, X.lof_mem_gradedResolutionPiece 1 F, ?_⟩
  intro hz
  have hz' : DirectSum.lof (ZMod 2) ℕ (fun n ↦ (resolutionX X (n + 1)).V) 2
      ((d X 2).hom F) = 0 := by
    have hz0 : X.gradedResolutionDifferential z = 0 := hz
    dsimp only [z] at hz0
    rw [gradedResolutionDifferential_lof] at hz0
    exact hz0
  have hd : (d X 2).hom F = 0 :=
    (DirectSum.of_injective 2) (hz'.trans
      (map_zero (DirectSum.lof (ZMod 2) ℕ (fun n ↦ (resolutionX X (n + 1)).V) 2)).symm)
  have hv := congrArg (fun F : (resolutionX X 3).V ↦ F 1 1 1) hd
  rw [hom_d_succ_apply_apply X 1] at hv
  simp only [ContinuousMap.sub_apply] at hv
  rw [hom_d_succ_apply_apply X 0] at hv
  simp [F, d_zero, ContRepresentation.coind₁ι_toFun] at hv

end TopRep

namespace TauCeti

universe u v w

variable {R : Type u} [Ring R] [TopologicalSpace R] [DiscreteTopology R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

/-- The total shifted coinduced resolution, as a functor on smooth discrete coefficient
representations. -/
@[expose] noncomputable def smoothGradedResolutionFunctor :
    SmoothDiscreteTopRep.{u, v, max v w} R G ⥤
      SmoothDiscreteTopRep.{u, v, max v w} R G where
  obj A := ⟨A.obj.gradedResolutionTopRep,
    A.obj.isSmoothDiscrete_gradedResolutionTopRep A.property⟩
  map f := ObjectProperty.homMk (TopRep.gradedResolutionTopRepMap f.hom)
  map_id A := ObjectProperty.hom_ext _ A.obj.gradedResolutionTopRepMap_id
  map_comp f g := ObjectProperty.hom_ext _
    (TopRep.gradedResolutionTopRepMap_comp f.hom g.hom)

/-- The smooth total-resolution functor sends a coefficient object to its total shifted
coinduced resolution.

This is not a simp lemma: rewriting the objects would take the morphism-evaluation lemmas, such as
`smoothGradedResolutionAugmentationApp_hom_apply`, out of simp-normal form. -/
theorem smoothGradedResolutionFunctor_obj (A : SmoothDiscreteTopRep.{u, v, max v w} R G) :
    (smoothGradedResolutionFunctor (R := R) (G := G)).obj A =
      ⟨A.obj.gradedResolutionTopRep, A.obj.isSmoothDiscrete_gradedResolutionTopRep A.property⟩ :=
  rfl

/-- The action on the object of the smooth total-resolution functor is the action on the total
shifted coinduced resolution. -/
@[simp]
theorem smoothGradedResolutionFunctor_obj_obj_ρ_apply
    (A : SmoothDiscreteTopRep.{u, v, max v w} R G) (g : G)
    (x : ((smoothGradedResolutionFunctor (R := R) (G := G)).obj A).obj.V) :
    ((smoothGradedResolutionFunctor (R := R) (G := G)).obj A).obj.ρ g x =
      A.obj.gradedResolutionTopRep.ρ g x :=
  rfl

/-- The smooth total-resolution functor acts on morphisms by the induced map of total
resolutions. -/
@[simp]
theorem smoothGradedResolutionFunctor_map {A B : SmoothDiscreteTopRep.{u, v, max v w} R G}
    (f : A ⟶ B) :
    (smoothGradedResolutionFunctor (R := R) (G := G)).map f =
      ObjectProperty.homMk (TopRep.gradedResolutionTopRepMap f.hom) :=
  rfl

/-- The coefficient augmentation into the total shifted coinduced resolution. -/
noncomputable def smoothGradedResolutionAugmentationApp
    (A : SmoothDiscreteTopRep.{u, v, max v w} R G) :
    A ⟶ (smoothGradedResolutionFunctor (R := R) (G := G)).obj A :=
  ObjectProperty.homMk A.obj.gradedResolutionTopRepAugmentation

/-- The coefficient augmentations into the total shifted coinduced resolution are natural among
smooth discrete coefficient representations. -/
noncomputable def smoothGradedResolutionAugmentation :
    𝟭 (SmoothDiscreteTopRep.{u, v, max v w} R G) ⟶
      smoothGradedResolutionFunctor (R := R) (G := G) where
  app A := smoothGradedResolutionAugmentationApp A
  naturality := fun {_ _} f ↦
    (ObjectProperty.hom_ext _
      (TopRep.gradedResolutionTopRepMap_augmentation f.hom)).symm

/-- The component of the smooth total-resolution augmentation is the named augmentation. -/
@[simp]
theorem smoothGradedResolutionAugmentation_app (A : SmoothDiscreteTopRep.{u, v, max v w} R G) :
    (smoothGradedResolutionAugmentation (R := R) (G := G)).app A =
      smoothGradedResolutionAugmentationApp A :=
  congrArg (fun α ↦ α.app A) smoothGradedResolutionAugmentation.eq_1

/-- The smooth total-resolution augmentation acts by the ordinary augmentation on carriers. -/
@[simp]
theorem smoothGradedResolutionAugmentationApp_hom_apply
    (A : SmoothDiscreteTopRep.{u, v, max v w} R G) (x : A.obj.V) :
    (smoothGradedResolutionAugmentationApp A).hom.hom x =
      A.obj.gradedResolutionAugmentation x :=
  (rfl)

/-- The differential of the total shifted coinduced resolution, as an endomorphism of the smooth
total resolution. -/
noncomputable def smoothGradedResolutionDifferential
    (A : SmoothDiscreteTopRep.{u, v, max v w} R G) :
    (smoothGradedResolutionFunctor (R := R) (G := G)).obj A ⟶
      (smoothGradedResolutionFunctor (R := R) (G := G)).obj A :=
  ObjectProperty.homMk A.obj.gradedResolutionTopRepDifferential

/-- The smooth total-resolution differential acts by the ordinary total differential on
carriers. -/
@[simp]
theorem smoothGradedResolutionDifferential_hom_apply
    (A : SmoothDiscreteTopRep.{u, v, max v w} R G) (x : A.obj.gradedResolutionModule) :
    (smoothGradedResolutionDifferential A).hom.hom x = A.obj.gradedResolutionDifferential x :=
  (rfl)

end TauCeti
