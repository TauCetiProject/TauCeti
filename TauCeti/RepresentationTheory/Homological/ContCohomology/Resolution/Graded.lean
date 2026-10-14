/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.CochainComplex.DirectSum
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CompactDiscrete
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.Basic
public import TauCeti.RepresentationTheory.Continuous.TopRep.Discrete
public import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality

/-!
# The graded module of the coinduced resolution

The shifted canonical resolution has degree-`n` term `C(G, …, C(G, X))`, with `n + 1`
function-space layers. Its external direct sum carries the canonical square-zero differential
of degree one and the componentwise `G`-action. The augmentation includes `X` as constant
functions in degree zero. Coefficient morphisms act degreewise through Mathlib's resolution maps.

For a compact group and smooth discrete coefficients, the total module with its discrete topology
is again smooth. This provides a graded coefficient module for finite tensor induction of
resolutions; tensor products can apply the differential on one carrier while tracking its degree.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Transactions of the American Mathematical Society 108 (1963), §§2–5.
* Mathlib's `TopRep.resolution'`, `ContinuousCohomology.resolutionMap`, and
  `Representation.directSum` supply the resolution, coefficient maps, and total action.

The canonical inclusion equations are named rewrites: automatic simplification of the iterated
function-space presentations need not retain the caller's scalar-instance presentation.
-/

public section

open CategoryTheory
open scoped DirectSum

namespace TopRep

universe u v w

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (X : TopRep.{max v w} R G)

private abbrev resolutionModuleComplex : CochainComplex (ModuleCat R) ℕ :=
  ((toActionTopModFunc ⋙ Action.forget (TopModuleCat R) G ⋙
    forget₂ (TopModuleCat R) (ModuleCat R)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (resolution' X)

private theorem resolutionModuleComplex_d (n : ℕ) :
    ((resolutionModuleComplex X).d n (n + 1)).hom =
      (d X (n + 1)).hom.toContinuousLinearMap.toLinearMap := by
  dsimp only [resolutionModuleComplex, Functor.mapHomologicalComplex, resolution']
  rw [CochainComplex.of_d, resolution'd_eq]
  rfl

/-- The direct sum of the shifted coinduced resolution. Degree zero is `C(G, X)`. -/
abbrev gradedResolutionModule := ⨁ n : ℕ, (resolutionX X (n + 1)).V

/-- The canonical differential on the total shifted resolution. -/
def gradedResolutionDifferential : X.gradedResolutionModule →ₗ[R] X.gradedResolutionModule :=
  (resolutionModuleComplex X).directSumDifferential

/-- On degree `n`, the total differential is the original resolution differential `d (n + 1)`. -/
theorem gradedResolutionDifferential_lof [DecidableEq ℕ] (n : ℕ) (x : (resolutionX X (n + 1)).V) :
    X.gradedResolutionDifferential
        (DirectSum.lof R ℕ (fun n ↦ (resolutionX X (n + 1)).V) n x) =
      DirectSum.lof R ℕ (fun n ↦ (resolutionX X (n + 1)).V) (n + 1)
        ((d X (n + 1)).hom x) := by
  -- The mapped complex retains the original term instances; `convert` identifies its
  -- bundled terms with the raw resolution carriers before using the differential equation.
  convert (resolutionModuleComplex X).directSumDifferential_lof n x using 1
  · rfl
  · rfl
  · rw [resolutionModuleComplex_d]
    rfl

/-- The differential of the total shifted resolution squares to zero. -/
theorem gradedResolutionDifferential_sq (x : X.gradedResolutionModule) :
    X.gradedResolutionDifferential (X.gradedResolutionDifferential x) = 0 :=
  (resolutionModuleComplex X).directSumDifferential_sq x

/-- The integer homogeneous-piece family of the total resolution, zero in negative degrees. -/
def gradedResolutionPiece : ℤ → Submodule R X.gradedResolutionModule :=
  (resolutionModuleComplex X).directSumPiece

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
theorem gradedResolutionDifferential_isHomogeneous :
    TauCeti.LinearMap.IsHomogeneous X.gradedResolutionDifferential X.gradedResolutionPiece
      X.gradedResolutionPiece 1 :=
  (resolutionModuleComplex X).directSumDifferential_isHomogeneous

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
theorem gradedResolutionRepresentation_isHomogeneous (g : G) :
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

private def resolutionModuleMap (f : X ⟶ Y) :
    resolutionModuleComplex X ⟶ resolutionModuleComplex Y :=
  CochainComplex.ofHom (fun n ↦
    let g := _root_.ContinuousCohomology.resolutionMap (ContinuousMonoidHom.id G) f (n + 1)
    ModuleCat.ofHom g.hom.toContinuousLinearMap.toLinearMap) fun n ↦ by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    dsimp only [resolutionModuleComplex, Functor.mapHomologicalComplex, resolution']
    rw [CochainComplex.of_d, CochainComplex.of_d, resolution'd_eq, resolution'd_eq]
    -- The forgetful functors retain the actual resolution module structures and linear maps.
    change (d Y (n + 1)).hom
        ((_root_.ContinuousCohomology.resolutionMap (ContinuousMonoidHom.id G) f (n + 1)).hom x) =
      (_root_.ContinuousCohomology.resolutionMap (ContinuousMonoidHom.id G) f (n + 1 + 1)).hom
        ((d X (n + 1)).hom x)
    have h := congrArg (fun g ↦ g.hom x)
      (_root_.ContinuousCohomology.resolutionMap_comp_d (ContinuousMonoidHom.id G) f (n + 1))
    convert h using 1 <;> rfl

/-- The degreewise coefficient map on the total shifted resolution. -/
def gradedResolutionMap (f : X ⟶ Y) : X.gradedResolutionModule →ₗ[R] Y.gradedResolutionModule :=
  CochainComplex.directSumMap (resolutionModuleMap f)

/-- A coefficient map acts on an included term by Mathlib's canonical resolution map. -/
theorem gradedResolutionMap_lof [DecidableEq ℕ] (f : X ⟶ Y) (n : ℕ)
    (x : (resolutionX X (n + 1)).V) :
    gradedResolutionMap f
      (DirectSum.lof R ℕ (fun n ↦ (resolutionX X (n + 1)).V) n x) =
      DirectSum.lof R ℕ (fun n ↦ (resolutionX Y (n + 1)).V) n
        ((_root_.ContinuousCohomology.resolutionMap (ContinuousMonoidHom.id G)
          f (n + 1)).hom x) := by
  -- As for the differential, the generic map uses the mapped complex's bundled term carriers.
  convert CochainComplex.directSumMap_lof (resolutionModuleMap f) n x using 1
  · rfl
  · rfl
  · rfl

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
  have h := congrArg (fun g ↦ g.hom x)
    (_root_.ContinuousCohomology.resolutionMap_comp_d (ContinuousMonoidHom.id G) f 0)
  convert congrArg (DirectSum.lof R ℕ (fun n ↦ (resolutionX Y (n + 1)).V) 0) h.symm using 1 <;>
    rfl

/-- Coefficient maps preserve the homogeneous degrees of the total resolution. -/
theorem gradedResolutionMap_isHomogeneous (f : X ⟶ Y) :
    TauCeti.LinearMap.IsHomogeneous (gradedResolutionMap f) X.gradedResolutionPiece
      Y.gradedResolutionPiece 0 :=
  CochainComplex.directSumMap_isHomogeneous (resolutionModuleMap f)

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
    have h := hom_comm_apply
      (_root_.ContinuousCohomology.resolutionMap (ContinuousMonoidHom.id G) f (n + 1)) g x
    convert congrArg (DirectSum.lof R ℕ (fun n ↦ (resolutionX Y (n + 1)).V) n) h using 1
    rfl
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

section Discrete

variable [DiscreteTopology R]

/-- The total resolution with its discrete topology. The body is exposed to retain the actual
direct-sum carrier and its module instances in statements about the action and tensor powers. -/
@[expose] noncomputable def gradedResolutionTopRep : TopRep.{max v w} R G :=
  TauCeti.discreteTopRep R G (Rep.of X.gradedResolutionRepresentation)

/-- The bundled discrete representation retains the total resolution carrier. -/
@[simp]
theorem gradedResolutionTopRep_V : X.gradedResolutionTopRep.V = X.gradedResolutionModule :=
  (rfl)

/-- The bundled action is the componentwise resolution action. This is a named rewrite:
rewriting before the homogeneous-inclusion equation can leave incompatible scalar presentations. -/
theorem gradedResolutionTopRep_ρ_apply (g : G) (x : X.gradedResolutionModule) :
    X.gradedResolutionTopRep.ρ g x = X.gradedResolutionRepresentation g x :=
  (rfl)

/-- The bundled discrete action on a homogeneous inclusion is the original resolution action.
This named equation retains the caller's scalar and resolution-term presentations. -/
theorem gradedResolutionTopRep_ρ_lof [DecidableEq ℕ] (n : ℕ) (g : G)
    (x : (resolutionX X (n + 1)).V) :
    X.gradedResolutionTopRep.ρ g
      (DirectSum.lof R ℕ (fun n ↦ (resolutionX X (n + 1)).V) n x) =
        DirectSum.lof R ℕ (fun n ↦ (resolutionX X (n + 1)).V) n
          ((resolutionX X (n + 1)).ρ g x) := by
  rw [gradedResolutionTopRep_ρ_apply, gradedResolutionRepresentation_lof]

/-- The total resolution carries the discrete topology. -/
instance : DiscreteTopology X.gradedResolutionTopRep.V := by
  unfold gradedResolutionTopRep
  infer_instance

/-- Over a compact group, the total coinduced resolution of smooth discrete coefficients is
smooth: each element has finitely many components, whose open stabilizers have open intersection. -/
theorem gradedResolutionTopRep_isSmoothDiscrete [CompactSpace G]
    (hX : TauCeti.IsSmoothDiscrete R X) :
    TauCeti.IsSmoothDiscrete R X.gradedResolutionTopRep := by
  let : DistribMulAction G X.gradedResolutionModule :=
    X.gradedResolutionTopRep.distribMulAction
  refine ⟨inferInstance, fun z ↦ ?_⟩
  -- The induction is on the raw direct-sum carrier, with the bundled object's action.
  change IsOpen {g : G | X.gradedResolutionRepresentation g z = z}
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
    -- Express the raw action as a stabilizer subgroup so openness passes to a larger subgroup.
    change IsOpen (MulAction.stabilizer G (x + y) : Set G)
    apply Subgroup.isOpen_mono (H₁ := MulAction.stabilizer G x ⊓ MulAction.stabilizer G y)
    · intro g hg
      simp only [Subgroup.mem_inf, MulAction.mem_stabilizer_iff] at hg ⊢
      simp [smul_add, hg.1, hg.2]
    · -- The action is installed on the raw carrier to avoid changing its scalar instances.
      change IsOpen ({g : G | g • x = x} ∩ {g : G | g • y = y})
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
