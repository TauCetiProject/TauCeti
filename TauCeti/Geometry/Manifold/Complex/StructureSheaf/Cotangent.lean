/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.MaximalIdeal
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.LocalRing
public import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.LinearAlgebra.Dual.Basis

/-!
# The cotangent space of a holomorphic stalk

Differentiating a holomorphic germ in a chart identifies the algebraic cotangent space
`𝔪/𝔪²` of its local ring with the complex dual of the model space. Scalars on the source
are in the native residue field; `holomorphicCotangentEquiv` is semilinear along its
canonical identification with `ℂ` by evaluation. No additional stalk or quotient carrier
is introduced.

The identification sends centered linear coordinate germs to their coordinate functionals.
In particular the coordinate classes form a basis, which describes the first-order
independence of local holomorphic parameters. The construction uses Hadamard's lemma
and the square-ideal criterion from `StructureSheaf.MaximalIdeal`.

## References

* R. C. Gunning and H. Rossi, *Analytic Functions of Several Complex Variables*, Chapter II.
* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter II.
-/

public noncomputable section

open Filter Function IsManifold Topology
open scoped ContDiff Manifold
open TauCeti TauCeti.holomorphicStructureSheaf

namespace OpenPartialHomeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  (e : OpenPartialHomeomorph X E) (x : X) (hx : x ∈ e.source)

/-- The complex derivative of a holomorphic germ, read in the chart `e`. -/
def holomorphicStalkFDeriv
    (s : (holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x) : StrongDual ℂ E :=
  (toFilterGerm 𝓘(ℂ, E) X x (𝓝 x) le_rfl s).liftOn
    (fun f ↦ fderiv ℂ (f ∘ e.symm) (e x)) fun _ _ h ↦
      (h.comp_tendsto (by
        simpa only [e.left_inv hx] using
          (e.continuousAt_symm (e.map_source hx)).tendsto)).fderiv_eq

/-- The derivative of a germ can be computed using any neighbourhood representative. -/
theorem holomorphicStalkFDeriv_eq
    {s : (holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x} {f : X → ℂ}
    (hf : toFilterGerm 𝓘(ℂ, E) X x (𝓝 x) le_rfl s = f) :
    e.holomorphicStalkFDeriv x hx s = fderiv ℂ (f ∘ e.symm) (e x) := by
  rw [holomorphicStalkFDeriv, hf]
  rfl

@[simp]
theorem holomorphicStalkFDeriv_zero : e.holomorphicStalkFDeriv x hx 0 = 0 := by
  rw [holomorphicStalkFDeriv_eq e x hx (f := 0) (by simp)]
  simp [Function.comp_def]

@[simp]
theorem holomorphicStalkFDeriv_one : e.holomorphicStalkFDeriv x hx 1 = 0 := by
  rw [holomorphicStalkFDeriv_eq e x hx (f := 1) (by simp)]
  simp [Function.comp_def]

variable (he : e ∈ maximalAtlas 𝓘(ℂ, E) ω X)

include he in
/-- Differentiation of holomorphic germs is additive. -/
@[simp]
theorem holomorphicStalkFDeriv_add
    (s t : (holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x) :
    e.holomorphicStalkFDeriv x hx (s + t) =
      e.holomorphicStalkFDeriv x hx s + e.holomorphicStalkFDeriv x hx t := by
  obtain ⟨f, -, hf⟩ := exists_toFilterGerm_eq x s
  obtain ⟨g, -, hg⟩ := exists_toFilterGerm_eq x t
  rw [holomorphicStalkFDeriv_eq e x hx (by rw [map_add, hf, hg, ← Germ.coe_add]),
    holomorphicStalkFDeriv_eq e x hx (hf _ _), holomorphicStalkFDeriv_eq e x hx (hg _ _)]
  exact fderiv_add (e.analyticAt_comp_symm_of_toFilterGerm_eq he hx (hf _ _)).differentiableAt
    (e.analyticAt_comp_symm_of_toFilterGerm_eq he hx (hg _ _)).differentiableAt

include he in
/-- Differentiation of holomorphic germs commutes with negation. -/
@[simp]
theorem holomorphicStalkFDeriv_neg
    (s : (holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x) :
    e.holomorphicStalkFDeriv x hx (-s) = -e.holomorphicStalkFDeriv x hx s := by
  apply eq_neg_of_add_eq_zero_left
  rw [← e.holomorphicStalkFDeriv_add x hx he, neg_add_cancel, holomorphicStalkFDeriv_zero]

include he in
/-- Differentiation of holomorphic germs commutes with subtraction. -/
@[simp]
theorem holomorphicStalkFDeriv_sub
    (s t : (holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x) :
    e.holomorphicStalkFDeriv x hx (s - t) =
      e.holomorphicStalkFDeriv x hx s - e.holomorphicStalkFDeriv x hx t := by
  simp only [sub_eq_add_neg, e.holomorphicStalkFDeriv_add x hx he,
    e.holomorphicStalkFDeriv_neg x hx he]

include he in
/-- The Leibniz rule for the derivative of holomorphic germs. -/
theorem holomorphicStalkFDeriv_mul
    (s t : (holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x) :
    e.holomorphicStalkFDeriv x hx (s * t) =
      eval 𝓘(ℂ, E) X x s • e.holomorphicStalkFDeriv x hx t +
        eval 𝓘(ℂ, E) X x t • e.holomorphicStalkFDeriv x hx s := by
  obtain ⟨f, -, hf⟩ := exists_toFilterGerm_eq x s
  obtain ⟨g, -, hg⟩ := exists_toFilterGerm_eq x t
  rw [holomorphicStalkFDeriv_eq e x hx (by rw [map_mul, hf, hg, ← Germ.coe_mul]),
    holomorphicStalkFDeriv_eq e x hx (hf _ _), holomorphicStalkFDeriv_eq e x hx (hg _ _),
    eval_eq_of_toFilterGerm_eq (hf _ _), eval_eq_of_toFilterGerm_eq (hg _ _)]
  simpa only [Function.comp_def, Pi.mul_def, e.left_inv hx] using
    fderiv_mul (e.analyticAt_comp_symm_of_toFilterGerm_eq he hx (hf _ _)).differentiableAt
      (e.analyticAt_comp_symm_of_toFilterGerm_eq he hx (hg _ _)).differentiableAt

/-- Centered linear coordinates have the prescribed derivative. -/
@[simp]
theorem holomorphicStalkFDeriv_holomorphicLinearCoordinateGerm (ℓ : StrongDual ℂ E) :
    e.holomorphicStalkFDeriv x hx (e.holomorphicLinearCoordinateGerm he x ℓ hx) = ℓ := by
  rw [holomorphicStalkFDeriv_eq e x hx
    (e.toFilterGerm_holomorphicLinearCoordinateGerm he x ℓ hx le_rfl)]
  have h : (fun y ↦ ℓ (e y - e x)) ∘ e.symm =ᶠ[𝓝 (e x)] fun z ↦ ℓ (z - e x) := by
    filter_upwards [e.open_target.mem_nhds (e.map_source hx)] with z hz
    simp [e.right_inv hz]
  rw [h.fderiv_eq]
  simpa only [Function.comp_def, map_sub, id_eq, ContinuousLinearMap.comp_id] using
    (ℓ.hasFDerivAt.comp (e x) ((hasFDerivAt_id (e x)).sub_const (e x))).fderiv

/-- Differentiation on the maximal ideal, semilinear along evaluation of germs. -/
private def holomorphicMaximalIdealFDeriv :
    IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x)
      →ₛₗ[eval 𝓘(ℂ, E) X x] StrongDual ℂ E where
  toFun s := e.holomorphicStalkFDeriv x hx s
  map_add' s t := e.holomorphicStalkFDeriv_add x hx he s t
  map_smul' a s := by
    have hs : eval 𝓘(ℂ, E) X x s = 0 := by
      simpa only [maximalIdeal_stalk, RingHom.mem_ker] using s.property
    have h := e.holomorphicStalkFDeriv_mul x hx he a s
    rw [hs] at h
    -- Evaluate pointwise: zero_smul does not simplify this continuous-dual action directly.
    ext v
    simpa only [_root_.add_apply, _root_.smul_apply, smul_eq_mul,
      zero_mul, add_zero, Submodule.coe_smul] using
      congrArg (fun L : StrongDual ℂ E ↦ L v) h

@[simp]
private theorem holomorphicMaximalIdealFDeriv_apply
    (s : IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x)) :
    e.holomorphicMaximalIdealFDeriv x hx he s = e.holomorphicStalkFDeriv x hx s := (rfl)

variable [FiniteDimensional ℂ E]

include he in
/-- The derivative identifies vanishing to second order in the holomorphic stalk. -/
theorem holomorphicStalkFDeriv_eq_zero_iff
    (s : IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x)) :
    e.holomorphicStalkFDeriv x hx s = 0 ↔
      (s : (holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x) ∈
        IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x) ^ 2 := by
  obtain ⟨f, -, hf⟩ := exists_toFilterGerm_eq x
    (s : (holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x)
  have hs : f x = 0 := by
    rw [← eval_eq_of_toFilterGerm_eq (hf _ _)]
    simpa only [maximalIdeal_stalk, RingHom.mem_ker] using s.property
  simp only [holomorphicStalkFDeriv_eq e x hx (hf _ _), maximalIdeal_stalk,
    e.mem_ker_eval_sq_iff he hx (hf _ _), hs, true_and]

/-- The derivative on the native algebraic cotangent space, semilinear along evaluation. -/
private def holomorphicCotangentMap :
    IsLocalRing.CotangentSpace ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x)
      →ₛₗ[eval 𝓘(ℂ, E) X x] StrongDual ℂ E :=
  Submodule.liftQ _ (e.holomorphicMaximalIdealFDeriv x hx he) fun s hs ↦
    (e.holomorphicStalkFDeriv_eq_zero_iff x hx he s).2
      ((Ideal.mem_toCotangent_ker _).1 (by
        rw [Ideal.toCotangent, Submodule.ker_mkQ]
        exact hs))

/-- The cotangent map sends the class of a germ to its derivative. -/
@[simp]
private theorem holomorphicCotangentMap_toCotangent
    (s : IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x)) :
    e.holomorphicCotangentMap x hx he (Ideal.toCotangent _ s) =
      e.holomorphicStalkFDeriv x hx s := (rfl)

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- The algebraic cotangent space of a holomorphic stalk is the complex dual of the model.
The scalar comparison is evaluation on the native residue field. -/
def holomorphicCotangentEquiv :
    LinearEquiv (RingHomClass.toRingHom (residueFieldEquiv 𝓘(ℂ, E) X x))
      (σ' := RingHomClass.toRingHom (residueFieldEquiv 𝓘(ℂ, E) X x).symm)
      (IsLocalRing.CotangentSpace ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x))
      (StrongDual ℂ E) :=
  LinearEquiv.ofBijective (σ₂₁ := RingHomClass.toRingHom (residueFieldEquiv 𝓘(ℂ, E) X x).symm)
    { toFun := e.holomorphicCotangentMap x hx he
      map_add' := map_add _
      map_smul' := fun c v ↦ by
        obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
        rw [RingHom.coe_coe, residueFieldEquiv_residue,
          ← IsLocalRing.ResidueField.algebraMap_eq,
          IsScalarTower.algebraMap_smul]
        exact (e.holomorphicCotangentMap x hx he).map_smulₛₗ a v }
    ⟨by
      rw [injective_iff_map_eq_zero]
      intro v hv
      obtain ⟨s, rfl⟩ := Ideal.toCotangent_surjective _ v
      exact (Ideal.toCotangent_eq_zero _ s).2
        ((e.holomorphicStalkFDeriv_eq_zero_iff x hx he s).1 hv),
      fun ℓ ↦ ⟨Ideal.toCotangent _
        ⟨e.holomorphicLinearCoordinateGerm he x ℓ hx, by simp⟩, by simp⟩⟩

/-- The cotangent equivalence is differentiation on representatives. -/
@[simp]
theorem holomorphicCotangentEquiv_toCotangent
    (s : IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x)) :
    e.holomorphicCotangentEquiv x hx he (Ideal.toCotangent _ s) =
      e.holomorphicStalkFDeriv x hx s := (rfl)

/-- The inverse cotangent equivalence takes a linear functional to its coordinate germ class. -/
@[simp]
theorem holomorphicCotangentEquiv_symm_apply (ℓ : StrongDual ℂ E) :
    (e.holomorphicCotangentEquiv x hx he).symm ℓ =
      Ideal.toCotangent _ ⟨e.holomorphicLinearCoordinateGerm he x ℓ hx, by simp⟩ := by
  apply (e.holomorphicCotangentEquiv x hx he).injective
  simp

/-- The basis of the cotangent space over the residue field given by the classes of
centered coordinates, for every basis of the finite-dimensional chart model. -/
def holomorphicCotangentBasis {ι : Type*} (b : Module.Basis ι ℂ E) :
    Module.Basis ι
      (IsLocalRing.ResidueField ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x))
      (IsLocalRing.CotangentSpace ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x)) := by
  classical
  have := Module.Finite.finite_basis b
  let σ := residueFieldEquiv 𝓘(ℂ, E) X x
  let := Module.compHom (StrongDual ℂ E) (RingHomClass.toRingHom σ)
  -- The compHom action unfolds to σ c • ℓ, so semilinearity gives linearity here.
  let d : IsLocalRing.CotangentSpace
      ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x) ≃ₗ[_] StrongDual ℂ E :=
    { (e.holomorphicCotangentEquiv x hx he).toAddEquiv with
      map_smul' := (e.holomorphicCotangentEquiv x hx he).map_smulₛₗ }
  let B := (b.dualBasis.map LinearMap.toContinuousLinearMap).mapCoeffs σ.symm
    (fun c v ↦ by
      -- The new scalar action is restriction along the residue-field comparison.
      exact congrArg (fun a : ℂ ↦ a • v) (σ.apply_symm_apply c))
  exact B.map d.symm

/-- Differentiation sends the coordinate cotangent basis to the coordinate functionals. -/
-- Simplify before expanding the basis vector into a coordinate germ class.
@[simp↓]
theorem holomorphicCotangentEquiv_holomorphicCotangentBasis
    {ι : Type*} (b : Module.Basis ι ℂ E) (i : ι) :
    e.holomorphicCotangentEquiv x hx he (e.holomorphicCotangentBasis x hx he b i) =
      LinearMap.toContinuousLinearMap (b.coord i) := by
  simp [holomorphicCotangentBasis, Module.Basis.mapCoeffs_apply, Module.Basis.coe_dualBasis]

/-- The coordinate cotangent basis consists of the centered coordinate germ classes. -/
@[simp]
theorem holomorphicCotangentBasis_apply {ι : Type*} (b : Module.Basis ι ℂ E) (i : ι) :
    e.holomorphicCotangentBasis x hx he b i = Ideal.toCotangent _
      ⟨e.holomorphicLinearCoordinateGerm he x
        (LinearMap.toContinuousLinearMap (b.coord i)) hx, by simp⟩ := by
  apply (e.holomorphicCotangentEquiv x hx he).injective
  simp

include hx he in
/-- The embedding dimension of a holomorphic stalk equals the complex dimension of its
manifold model. This does not require Noetherianity of the stalk. -/
theorem finrank_cotangentSpace_holomorphicStalk :
    Module.finrank
        (IsLocalRing.ResidueField ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x))
        (IsLocalRing.CotangentSpace ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x)) =
      Module.finrank ℂ E := by
  simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis
    (e.holomorphicCotangentBasis x hx he (Module.finBasis ℂ E))

end OpenPartialHomeomorph
