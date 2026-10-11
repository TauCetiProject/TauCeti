/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Basic
public import TauCeti.Algebra.TensorProduct.Module
public import TauCeti.Algebra.Module.GradedModule.Opposite
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Actions
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Linear.FunctorCategory

/-!
# Balanced tensor composition of graded bimodules

For graded algebras `A`, `B`, and `C`, this file constructs the composition

`(A,B)-bimodules × (B,C)-bimodules → (A,C)-bimodules`,

balanced over `B`. Each bimodule is an object of `GradedModuleCat` over its
enveloping algebra, with the tensor-product internal grading. Restricting the
enveloping action supplies the actions used to balance. The quotient has the sum
internal grading and the two outer actions.

The construction uses the existing balanced quotient, grading, map, and lift APIs.
Its internal grading introduces no Koszul sign. Cohomological tensor signs come
from Mathlib's totalization when this bifunctor is applied to cochain complexes.
Taking all three algebras and gradings equal gives tensor composition of
endobimodules; heterogeneous composition also supplies the tensors needed for
transfer through a supplied Morita equivalence.

## References

* B. Keller, *Deriving DG categories*, Section 6.1.
-/

public section

open CategoryTheory MulOpposite
open scoped TensorProduct

namespace TauCeti.GradedModuleCat

universe v vM vN uk uA uB uC

variable {k : Type uk} {A : Type uA} {B : Type uB}
  [CommRing k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  (Γ : InternalGrading k A) (Δ : InternalGrading k B)

/-- The left action obtained by restricting the envelope action to its first factor. -/
local instance (M : GradedModuleCat.{v} (Γ.tensorProduct Δ.opposite).piece) : Module A M :=
  TauCeti.Algebra.TensorProduct.moduleLeft (k := k) (A := A) (B := Bᵐᵒᵖ) M

/-- The right action obtained by restricting the envelope action to its second factor. -/
local instance (M : GradedModuleCat.{v} (Γ.tensorProduct Δ.opposite).piece) : Module Bᵐᵒᵖ M :=
  TauCeti.Algebra.TensorProduct.moduleRight (k := k) (A := A) (B := Bᵐᵒᵖ) M

local instance (M : GradedModuleCat.{v} (Γ.tensorProduct Δ.opposite).piece) : IsScalarTower k A M :=
  TauCeti.Algebra.TensorProduct.moduleLeftIsScalarTower (k := k) (A := A) (B := Bᵐᵒᵖ) M

local instance (M : GradedModuleCat.{v} (Γ.tensorProduct Δ.opposite).piece) :
    IsScalarTower k Bᵐᵒᵖ M :=
  TauCeti.Algebra.TensorProduct.moduleRightIsScalarTower (k := k) (A := A) (B := Bᵐᵒᵖ) M

local instance (M : GradedModuleCat.{v} (Γ.tensorProduct Δ.opposite).piece) :
    SMulCommClass A Bᵐᵒᵖ M :=
  TauCeti.Algebra.TensorProduct.moduleSMulCommClass (k := k) (A := A) (B := Bᵐᵒᵖ) M

local instance [SetLike.GradedOne Δ.piece]
    (M : GradedModuleCat.{v} (Γ.tensorProduct Δ.opposite).piece) :
    SetLike.GradedSMul Γ.piece M.grading.piece where
  smul_mem {p q} {a m} ha hm := by
    -- Express the restricted action through its defining inclusion into the envelope.
    change (a ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • m ∈ M.grading.piece (p + q)
    have h1 : (1 : Bᵐᵒᵖ) ∈ Δ.opposite.piece 0 :=
      (Δ.mem_opposite_piece_iff 0 1).2 (SetLike.one_mem_graded Δ.piece)
    have h := Γ.tmul_mem_tensorProduct Δ.opposite ha h1
    rw [add_zero] at h
    exact SetLike.GradedSMul.smul_mem h hm

local instance rightGradedSMul [DirectSum.Decomposition Δ.piece]
    [SetLike.GradedOne Γ.piece] (M : GradedModuleCat.{v} (Γ.tensorProduct Δ.opposite).piece) :
    SetLike.GradedSMul (InternalGrading.ofDecomposition Δ.piece).opposite.piece
      M.grading.piece where
  smul_mem {p q} {a m} ha hm := by
    -- Express the restricted right action through the other envelope inclusion.
    change ((1 : A) ⊗ₜ[k] a) • m ∈ M.grading.piece (p + q)
    rw [InternalGrading.mem_opposite_piece_iff, InternalGrading.ofDecomposition_piece] at ha
    have ha' : a ∈ Δ.opposite.piece p := (Δ.mem_opposite_piece_iff p a).2 ha
    have h := Γ.tmul_mem_tensorProduct Δ.opposite (SetLike.one_mem_graded Γ.piece) ha'
    rw [zero_add] at h
    exact SetLike.GradedSMul.smul_mem h hm

variable {C : Type uC} [Ring C] [Algebra k C] (Θ : InternalGrading k C)

local notation "E" => A ⊗[k] Cᵐᵒᵖ

section Tensor

variable [GradedAlgebra Γ.piece] [GradedAlgebra Δ.piece] [GradedAlgebra Θ.piece]

variable (M : GradedModuleCat.{vM} (Γ.tensorProduct Δ.opposite).piece)
  (N : GradedModuleCat.{vN} (Δ.tensorProduct Θ.opposite).piece)

local notation "T" => BalancedTensorProduct k B M N

/-- The left outer action on the balanced tensor quotient. -/
local instance : Module A T := BalancedTensorProduct.leftModule A
/-- The right outer action on the balanced tensor quotient. -/
local instance : Module Cᵐᵒᵖ T := BalancedTensorProduct.rightModule Cᵐᵒᵖ
local instance : IsScalarTower k A T := BalancedTensorProduct.leftIsScalarTower A
local instance : IsScalarTower k Cᵐᵒᵖ T := BalancedTensorProduct.rightIsScalarTower Cᵐᵒᵖ
local instance : SMulCommClass A Cᵐᵒᵖ T :=
  BalancedTensorProduct.outerSMulCommClass A Cᵐᵒᵖ
/-- The commuting outer actions combine into an action of the output envelope. -/
local instance : Module E T := TensorProduct.Algebra.module

local instance : IsScalarTower k E T :=
  IsScalarTower.of_algebraMap_smul fun r z ↦ by
    rw [Algebra.TensorProduct.algebraMap_apply (R := k) (S := k) (A := A) (B := Cᵐᵒᵖ),
      TensorProduct.Algebra.smul_def (R := k) (A := A) (B := Cᵐᵒᵖ) (M := T), one_smul]
    exact IsScalarTower.algebraMap_smul A r z

local instance : SetLike.GradedSMul Γ.piece
    (BalancedTensorProduct.grading (𝒜 := Δ.piece) M.grading N.grading).piece :=
  BalancedTensorProduct.gradedSMul_left (𝒜 := Δ.piece) M.grading N.grading A Γ.piece

local instance : SetLike.GradedSMul (InternalGrading.ofDecomposition Θ.piece).opposite.piece
    (BalancedTensorProduct.grading (𝒜 := Δ.piece) M.grading N.grading).piece :=
  BalancedTensorProduct.gradedSMul_right (𝒜 := Δ.piece) M.grading N.grading Cᵐᵒᵖ
    (InternalGrading.ofDecomposition Θ.piece).opposite.piece

/-- The graded `(A,C)`-bimodule obtained by balancing over `B`. -/
noncomputable def bimoduleTensorObj :
    GradedModuleCat.{max vM vN} (Γ.tensorProduct Θ.opposite).piece where
  carrier := T
  grading := BalancedTensorProduct.grading (𝒜 := Δ.piece) M.grading N.grading
  gradedSMul := ⟨fun {p q} {a z} ha hz ↦ by
    rw [InternalGrading.tensorProduct_piece_eq_iSup] at ha
    refine (iSup_le fun r ↦ Submodule.map₂_le.mpr fun x hx y hy ↦ ?_ :
      _ ≤ ((BalancedTensorProduct.grading (𝒜 := Δ.piece) M.grading N.grading).piece
        (p + q)).comap (LinearMap.applyₗ (R := k) z ∘ₗ
          (Algebra.lsmul k k T (A := E)).toLinearMap)) ha
    simp only [Submodule.mem_comap, TensorProduct.mk_apply, LinearMap.comp_apply,
      LinearMap.applyₗ_apply_apply, AlgHom.toLinearMap_apply, Algebra.lsmul_apply,
      TensorProduct.Algebra.smul_def]
    have hy' : y ∈ (InternalGrading.ofDecomposition Θ.piece).opposite.piece (p - r) := by
      simpa only [InternalGrading.mem_opposite_piece_iff,
        InternalGrading.ofDecomposition_piece] using hy
    have h := SetLike.GradedSMul.smul_mem hx (SetLike.GradedSMul.smul_mem hy' hz)
    -- The envelope degrees are r and p - r, whose sum is p.
    simpa only [vadd_eq_add, show r + (p - r + q) = p + q by omega] using h⟩

/-- The pure tensor in the graded bimodule tensor product. -/
def bimoduleTensorTmul (m : M) (n : N) : bimoduleTensorObj Γ Δ Θ M N :=
  BalancedTensorProduct.tmul k B m n

/-- Forgetting the output grading identifies the tensor carrier with the balanced quotient.
The factor actions in this quotient are the restrictions of the enveloping actions. -/
noncomputable def bimoduleTensorUnderlyingEquiv :
    bimoduleTensorObj Γ Δ Θ M N ≃ₗ[k] BalancedTensorProduct k B M N :=
  LinearEquiv.refl k T

@[simp]
theorem bimoduleTensorUnderlyingEquiv_tmul (m : M) (n : N) :
    bimoduleTensorUnderlyingEquiv Γ Δ Θ M N (bimoduleTensorTmul Γ Δ Θ M N m n) =
      BalancedTensorProduct.tmul k B m n := (rfl)

@[simp]
theorem bimoduleTensorUnderlyingEquiv_symm_tmul (m : M) (n : N) :
    (bimoduleTensorUnderlyingEquiv Γ Δ Θ M N).symm (BalancedTensorProduct.tmul k B m n) =
      bimoduleTensorTmul Γ Δ Θ M N m n := (rfl)

@[simp]
theorem bimoduleTensorTmul_zero_left (n : N) :
    bimoduleTensorTmul Γ Δ Θ M N 0 n = 0 :=
  BalancedTensorProduct.zero_tmul k B n

@[simp]
theorem bimoduleTensorTmul_zero_right (m : M) :
    bimoduleTensorTmul Γ Δ Θ M N m 0 = 0 :=
  BalancedTensorProduct.tmul_zero k B m

@[simp]
theorem bimoduleTensorTmul_add_left (m m' : M) (n : N) :
    bimoduleTensorTmul Γ Δ Θ M N (m + m') n =
      bimoduleTensorTmul Γ Δ Θ M N m n + bimoduleTensorTmul Γ Δ Θ M N m' n :=
  BalancedTensorProduct.add_tmul k B m m' n

@[simp]
theorem bimoduleTensorTmul_add_right (m : M) (n n' : N) :
    bimoduleTensorTmul Γ Δ Θ M N m (n + n') =
      bimoduleTensorTmul Γ Δ Θ M N m n + bimoduleTensorTmul Γ Δ Θ M N m n' :=
  BalancedTensorProduct.tmul_add k B m n n'

@[simp]
theorem bimoduleTensorTmul_smul_left (r : k) (m : M) (n : N) :
    bimoduleTensorTmul Γ Δ Θ M N (r • m) n = r • bimoduleTensorTmul Γ Δ Θ M N m n :=
  BalancedTensorProduct.smul_tmul k B r m n

@[simp]
theorem bimoduleTensorTmul_smul_right (r : k) (m : M) (n : N) :
    bimoduleTensorTmul Γ Δ Θ M N m (r • n) = r • bimoduleTensorTmul Γ Δ Θ M N m n :=
  BalancedTensorProduct.tmul_smul k B r m n

/-- Internal degrees add on pure bimodule tensors. -/
theorem bimoduleTensorTmul_mem {p q : ℤ} {m : M} {n : N}
    (hm : m ∈ M.grading.piece p) (hn : n ∈ N.grading.piece q) :
    bimoduleTensorTmul Γ Δ Θ M N m n ∈ (bimoduleTensorObj Γ Δ Θ M N).grading.piece (p + q) :=
  BalancedTensorProduct.tmul_mem_grading (𝒜 := Δ.piece) M.grading N.grading hm hn

/-- Every bimodule tensor is a sum of pure tensors. -/
@[elab_as_elim]
theorem bimoduleTensor_induction_on {P : bimoduleTensorObj Γ Δ Θ M N → Prop}
    (z : bimoduleTensorObj Γ Δ Θ M N)
    (ht : ∀ m n, P (bimoduleTensorTmul Γ Δ Θ M N m n))
    (ha : ∀ x y, P x → P y → P (x + y)) : P z :=
  BalancedTensorProduct.induction_on k B z ht ha

/-- The quotient map from the ground-ring tensor product. -/
noncomputable def bimoduleTensorMkQ : M ⊗[k] N →ₗ[k] bimoduleTensorObj Γ Δ Θ M N :=
  BalancedTensorProduct.mkQ k B

@[simp]
theorem bimoduleTensorMkQ_tmul (m : M) (n : N) :
    bimoduleTensorMkQ Γ Δ Θ M N (m ⊗ₜ[k] n) = bimoduleTensorTmul Γ Δ Θ M N m n :=
  BalancedTensorProduct.mkQ_tmul k B m n

/-- The internal degree piece is the image of the ground-ring tensor degree piece. -/
theorem bimoduleTensorObj_grading_piece (p : ℤ) :
    (bimoduleTensorObj Γ Δ Θ M N).grading.piece p =
      ((M.grading.tensorProduct N.grading).piece p).map (bimoduleTensorMkQ Γ Δ Θ M N) :=
  BalancedTensorProduct.grading_piece M.grading N.grading p

/-- A homogeneous balanced tensor has a homogeneous ground-ring representative. -/
theorem mem_bimoduleTensorObj_piece_iff {p : ℤ} {z : bimoduleTensorObj Γ Δ Θ M N} :
    z ∈ (bimoduleTensorObj Γ Δ Θ M N).grading.piece p ↔
      ∃ x ∈ (M.grading.tensorProduct N.grading).piece p, bimoduleTensorMkQ Γ Δ Θ M N x = z :=
  BalancedTensorProduct.mem_grading_piece_iff M.grading N.grading

/-- Balancing moves the right `B`-action to the left `B`-action. -/
theorem bimoduleTensorTmul_balance (b : B) (m : M) (n : N) :
    bimoduleTensorTmul Γ Δ Θ M N (((1 : A) ⊗ₜ[k] op b) • m) n =
      bimoduleTensorTmul Γ Δ Θ M N m ((b ⊗ₜ[k] (1 : Cᵐᵒᵖ)) • n) :=
  BalancedTensorProduct.balance k B b m n

/-- A pure output enveloping scalar acts on the two outer factors. -/
@[simp]
theorem tmul_smul_bimoduleTensorTmul (a : A) (c : Cᵐᵒᵖ) (m : M) (n : N) :
    (a ⊗ₜ[k] c) • bimoduleTensorTmul Γ Δ Θ M N m n =
      bimoduleTensorTmul Γ Δ Θ M N ((a ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • m)
        (((1 : B) ⊗ₜ[k] c) • n) := by
  -- Compute the envelope action on the quotient using the two outer actions.
  change (a ⊗ₜ[k] c) • BalancedTensorProduct.tmul k B m n =
    BalancedTensorProduct.tmul k B (a • m) (c • n)
  rw [TensorProduct.Algebra.smul_def (R := k) (A := A) (B := Cᵐᵒᵖ)
    (M := BalancedTensorProduct k B M N)]
  simp only [BalancedTensorProduct.smul_tmul_right, BalancedTensorProduct.smul_tmul_left]

variable {M N}
  {M' M'' : GradedModuleCat.{vM} (Γ.tensorProduct Δ.opposite).piece}
  {N' N'' : GradedModuleCat.{vN} (Δ.tensorProduct Θ.opposite).piece}

private def tensorMapBase (f : M ⟶ M') (g : N ⟶ N') :
    BalancedTensorProduct k B M N →ₗ[k] BalancedTensorProduct k B M' N' :=
  BalancedTensorProduct.map (f.hom.restrictScalars k) (g.hom.restrictScalars k)
    (fun b m ↦ f.hom.map_smul ((1 : A) ⊗ₜ[k] op b) m)
    (fun b n ↦ g.hom.map_smul (b ⊗ₜ[k] (1 : Cᵐᵒᵖ)) n)

private noncomputable def tensorMapLinear (f : M ⟶ M') (g : N ⟶ N') :
    BalancedTensorProduct k B M N →ₗ[E] BalancedTensorProduct k B M' N' :=
  TauCeti.Algebra.TensorProduct.linearMapOfFactors (BalancedTensorProduct k B M N)
    (tensorMapBase Γ Δ Θ f g)
    (fun a z ↦ by
      have h : tensorMapBase Γ Δ Θ f g (a • z) = a • tensorMapBase Γ Δ Θ f g z :=
        BalancedTensorProduct.map_smul_left A
          (f.hom.restrictScalars k) (g.hom.restrictScalars k)
          (fun b m ↦ f.hom.map_smul ((1 : A) ⊗ₜ[k] op b) m)
          (fun b n ↦ g.hom.map_smul (b ⊗ₜ[k] (1 : Cᵐᵒᵖ)) n)
          (fun a m ↦ f.hom.map_smul (a ⊗ₜ[k] (1 : Bᵐᵒᵖ)) m) a z
      simpa only [TensorProduct.Algebra.smul_def, one_smul] using h)
    (fun c z ↦ by
      have h : tensorMapBase Γ Δ Θ f g (c • z) = c • tensorMapBase Γ Δ Θ f g z :=
        BalancedTensorProduct.map_smul_right Cᵐᵒᵖ
          (f.hom.restrictScalars k) (g.hom.restrictScalars k)
          (fun b m ↦ f.hom.map_smul ((1 : A) ⊗ₜ[k] op b) m)
          (fun b n ↦ g.hom.map_smul (b ⊗ₜ[k] (1 : Cᵐᵒᵖ)) n)
          (fun c n ↦ g.hom.map_smul ((1 : B) ⊗ₜ[k] c) n) c z
      simpa only [TensorProduct.Algebra.smul_def, one_smul] using h)

omit [GradedAlgebra Γ.piece] [GradedAlgebra Δ.piece] [GradedAlgebra Θ.piece] in
private theorem tensorMapLinear_apply (f : M ⟶ M') (g : N ⟶ N')
    (z : BalancedTensorProduct k B M N) :
    tensorMapLinear Γ Δ Θ f g z = tensorMapBase Γ Δ Θ f g z := by
  simp only [tensorMapLinear, TauCeti.Algebra.TensorProduct.linearMapOfFactors_apply]

private theorem tensorMapBase_mem (f : M ⟶ M') (g : N ⟶ N') {p : ℤ}
    {z : BalancedTensorProduct k B M N}
    (hz : z ∈ (BalancedTensorProduct.grading (𝒜 := Δ.piece) M.grading N.grading).piece p) :
    tensorMapBase Γ Δ Θ f g z ∈
      (BalancedTensorProduct.grading (𝒜 := Δ.piece) M'.grading N'.grading).piece p := by
  have hf : LinearMap.IsHomogeneous (f.hom.restrictScalars k)
      M.grading.piece M'.grading.piece 0 :=
    LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by simpa using map_mem f hx
  have hg : LinearMap.IsHomogeneous (g.hom.restrictScalars k)
      N.grading.piece N'.grading.piece 0 :=
    LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by simpa using map_mem g hx
  have h := BalancedTensorProduct.isHomogeneous_map (𝒜 := Δ.piece)
    M.grading N.grading M'.grading N'.grading
    (f.hom.restrictScalars k) (g.hom.restrictScalars k)
    (fun a m ↦ f.hom.map_smul ((1 : A) ⊗ₜ[k] op a) m)
    (fun a n ↦ g.hom.map_smul (a ⊗ₜ[k] (1 : Cᵐᵒᵖ)) n) hf hg
  simpa only [tensorMapBase, add_zero] using h.map_mem hz

/-- Tensor the degree-zero bimodule maps in both factors. -/
noncomputable def bimoduleTensorMap (f : M ⟶ M') (g : N ⟶ N') :
    bimoduleTensorObj Γ Δ Θ M N ⟶ bimoduleTensorObj Γ Δ Θ M' N' :=
  ofHom (tensorMapLinear Γ Δ Θ f g) (LinearMap.isHomogeneous_def.2
    -- Specify the quotient carrier before elaborating the degree-preservation proof.
    (show ∀ (p : ℤ) (z : BalancedTensorProduct k B M N),
      z ∈ (BalancedTensorProduct.grading (𝒜 := Δ.piece) M.grading N.grading).piece p →
      tensorMapLinear Γ Δ Θ f g z ∈
        (BalancedTensorProduct.grading (𝒜 := Δ.piece) M'.grading N'.grading).piece (p + 0) from
      fun p z hz ↦ by
        rw [tensorMapLinear_apply, add_zero]
        exact tensorMapBase_mem Γ Δ Θ f g hz))

@[simp]
theorem bimoduleTensorMap_tmul (f : M ⟶ M') (g : N ⟶ N') (m : M) (n : N) :
    (bimoduleTensorMap Γ Δ Θ f g).hom (bimoduleTensorTmul Γ Δ Θ M N m n) =
      bimoduleTensorTmul Γ Δ Θ M' N' (f.hom m) (g.hom n) := by
  -- Compute the bundled map on the quotient's pure-tensor constructor.
  change tensorMapLinear Γ Δ Θ f g (BalancedTensorProduct.tmul k B m n) = _
  rw [tensorMapLinear_apply]
  exact BalancedTensorProduct.map_tmul _ _ _ _ _ _

/-- Morphisms out of a bimodule tensor product agree if they agree on pure tensors. -/
@[ext]
theorem bimoduleTensor_hom_ext {P : GradedModuleCat.{max vM vN} (Γ.tensorProduct Θ.opposite).piece}
    {f g : bimoduleTensorObj Γ Δ Θ M N ⟶ P}
    (h : ∀ m n, f.hom (bimoduleTensorTmul Γ Δ Θ M N m n) =
      g.hom (bimoduleTensorTmul Γ Δ Θ M N m n)) : f = g := by
  apply hom_ext
  apply LinearMap.restrictScalars_injective k
  apply BalancedTensorProduct.hom_ext
  exact h

section Lift

variable {P : GradedModuleCat.{max vM vN} (Γ.tensorProduct Θ.opposite).piece}
  (f : M →ₗ[k] N →ₗ[k] P)
  (hbalance : ∀ (b : B) (m : M) (n : N),
    f (((1 : A) ⊗ₜ[k] op b) • m) n = f m ((b ⊗ₜ[k] (1 : Cᵐᵒᵖ)) • n))
  (hleft : ∀ (a : A) (m : M) (n : N),
    f ((a ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • m) n = (a ⊗ₜ[k] (1 : Cᵐᵒᵖ)) • f m n)
  (hright : ∀ (c : Cᵐᵒᵖ) (m : M) (n : N),
    f m (((1 : B) ⊗ₜ[k] c) • n) = ((1 : A) ⊗ₜ[k] c) • f m n)

private noncomputable def tensorLiftLinear :
    BalancedTensorProduct k B M N →ₗ[E] P :=
  TauCeti.Algebra.TensorProduct.linearMapOfFactors (BalancedTensorProduct k B M N)
    (BalancedTensorProduct.lift f hbalance)
    (fun a z ↦ by
      have h := BalancedTensorProduct.lift_smul_left A f hbalance hleft a z
      rw [TauCeti.Algebra.TensorProduct.smul_moduleLeft
        (k := k) (A := A) (B := Cᵐᵒᵖ) P] at h
      simpa only [TensorProduct.Algebra.smul_def, one_smul] using h)
    (fun c z ↦ by
      have h := BalancedTensorProduct.lift_smul_right Cᵐᵒᵖ f hbalance hright c z
      rw [TauCeti.Algebra.TensorProduct.smul_moduleRight
        (k := k) (A := A) (B := Cᵐᵒᵖ) P] at h
      simpa only [TensorProduct.Algebra.smul_def, one_smul] using h)

omit [GradedAlgebra Γ.piece] [GradedAlgebra Δ.piece] [GradedAlgebra Θ.piece] in
private theorem tensorLiftLinear_tmul (m : M) (n : N) :
    tensorLiftLinear Γ Δ Θ f hbalance hleft hright
      (BalancedTensorProduct.tmul k B m n) = f m n := by
  rw [tensorLiftLinear, TauCeti.Algebra.TensorProduct.linearMapOfFactors_apply]
  exact BalancedTensorProduct.lift_tmul f hbalance m n

variable (hdegree : ∀ {p q : ℤ} {m : M} {n : N},
  m ∈ M.grading.piece p → n ∈ N.grading.piece q → f m n ∈ P.grading.piece (p + q))

/-- Lift a balanced bilinear map that respects the two outer actions and internal degrees. -/
noncomputable def bimoduleTensorLift : bimoduleTensorObj Γ Δ Θ M N ⟶ P :=
  ofHom (tensorLiftLinear Γ Δ Θ f hbalance hleft hright)
    (LinearMap.isHomogeneous_def.2 fun p z hz ↦ by
      rw [add_zero]
      -- Use the quotient grading's span of homogeneous pure tensors.
      change z ∈ (BalancedTensorProduct.grading (𝒜 := Δ.piece) M.grading N.grading).piece p
        at hz
      rw [BalancedTensorProduct.grading_piece_eq_iSup] at hz
      refine (iSup_le fun q ↦ Submodule.map₂_le.mpr fun m hm n hn ↦ ?_ :
        _ ≤ (P.grading.piece p).comap
          ((tensorLiftLinear Γ Δ Θ f hbalance hleft hright).restrictScalars k)) hz
      rw [Submodule.mem_comap, BalancedTensorProduct.mk_apply,
        LinearMap.restrictScalars_apply, tensorLiftLinear_tmul]
      have h := hdegree hm hn
      -- The two input degrees q and p - q add to the output degree p.
      simpa only [show q + (p - q) = p by omega] using h)

@[simp]
theorem bimoduleTensorLift_tmul (m : M) (n : N) :
    (bimoduleTensorLift Γ Δ Θ f hbalance hleft hright hdegree).hom
      (bimoduleTensorTmul Γ Δ Θ M N m n) = f m n :=
  tensorLiftLinear_tmul Γ Δ Θ f hbalance hleft hright m n

/-- The homogeneous balanced lift is uniquely determined by its pure-tensor values. -/
theorem bimoduleTensorLift_unique (g : bimoduleTensorObj Γ Δ Θ M N ⟶ P)
    (h : ∀ m n, g.hom (bimoduleTensorTmul Γ Δ Θ M N m n) = f m n) :
    g = bimoduleTensorLift Γ Δ Θ f hbalance hleft hright hdegree := by
  apply bimoduleTensor_hom_ext Γ Δ Θ
  intro m n
  rw [bimoduleTensorLift_tmul]
  exact h m n

end Lift

@[simp]
theorem bimoduleTensorMap_id :
    bimoduleTensorMap Γ Δ Θ (𝟙 M) (𝟙 N) = 𝟙 (bimoduleTensorObj Γ Δ Θ M N) := by
  apply bimoduleTensor_hom_ext Γ Δ Θ
  intro m n
  simp

/-- Tensoring bimodule maps respects composition. -/
@[simp]
theorem bimoduleTensorMap_comp (f : M ⟶ M') (g : N ⟶ N')
    (f' : M' ⟶ M'') (g' : N' ⟶ N'') :
    bimoduleTensorMap Γ Δ Θ (f ≫ f') (g ≫ g') =
      bimoduleTensorMap Γ Δ Θ f g ≫ bimoduleTensorMap Γ Δ Θ f' g' := by
  apply bimoduleTensor_hom_ext Γ Δ Θ
  intro m n
  simp

@[simp]
theorem bimoduleTensorMap_add_left (f f' : M ⟶ M') (g : N ⟶ N') :
    bimoduleTensorMap Γ Δ Θ (f + f') g =
      bimoduleTensorMap Γ Δ Θ f g + bimoduleTensorMap Γ Δ Θ f' g := by
  apply bimoduleTensor_hom_ext Γ Δ Θ
  intro m n
  simp only [hom_add, LinearMap.add_apply, bimoduleTensorMap_tmul]
  exact BalancedTensorProduct.add_tmul k B _ _ _

@[simp]
theorem bimoduleTensorMap_add_right (f : M ⟶ M') (g g' : N ⟶ N') :
    bimoduleTensorMap Γ Δ Θ f (g + g') =
      bimoduleTensorMap Γ Δ Θ f g + bimoduleTensorMap Γ Δ Θ f g' := by
  apply bimoduleTensor_hom_ext Γ Δ Θ
  intro m n
  simp only [hom_add, LinearMap.add_apply, bimoduleTensorMap_tmul]
  exact BalancedTensorProduct.tmul_add k B _ _ _

@[simp]
theorem bimoduleTensorMap_smul_left (c : k) (f : M ⟶ M') (g : N ⟶ N') :
    bimoduleTensorMap Γ Δ Θ (c • f) g = c • bimoduleTensorMap Γ Δ Θ f g := by
  apply bimoduleTensor_hom_ext Γ Δ Θ
  intro m n
  simp only [hom_smul, LinearMap.smul_apply, bimoduleTensorMap_tmul]
  exact BalancedTensorProduct.smul_tmul k B _ _ _

@[simp]
theorem bimoduleTensorMap_smul_right (c : k) (f : M ⟶ M') (g : N ⟶ N') :
    bimoduleTensorMap Γ Δ Θ f (c • g) = c • bimoduleTensorMap Γ Δ Θ f g := by
  apply bimoduleTensor_hom_ext Γ Δ Θ
  intro m n
  simp only [hom_smul, LinearMap.smul_apply, bimoduleTensorMap_tmul]
  exact BalancedTensorProduct.tmul_smul k B _ _ _

/-- Balanced tensor composition of internally graded bimodules. -/
-- Expose the object assignment so the tensor maps have the computed source and target types.
@[expose]
noncomputable def bimoduleTensor :
    GradedModuleCat.{vM} (Γ.tensorProduct Δ.opposite).piece ⥤
      GradedModuleCat.{vN} (Δ.tensorProduct Θ.opposite).piece ⥤
        GradedModuleCat.{max vM vN} (Γ.tensorProduct Θ.opposite).piece where
  obj M :=
    { obj N := bimoduleTensorObj Γ Δ Θ M N
      map g := bimoduleTensorMap Γ Δ Θ (𝟙 M) g
      map_id N := bimoduleTensorMap_id Γ Δ Θ
      map_comp g g' := by
        rw [← bimoduleTensorMap_comp, Category.id_comp] }
  map f :=
    { app N := bimoduleTensorMap Γ Δ Θ f (𝟙 N)
      naturality N N' g := by
        -- Compute the components of the two curried tensor maps.
        change bimoduleTensorMap Γ Δ Θ (𝟙 _) g ≫ bimoduleTensorMap Γ Δ Θ f (𝟙 _) =
          bimoduleTensorMap Γ Δ Θ f (𝟙 _) ≫ bimoduleTensorMap Γ Δ Θ (𝟙 _) g
        simp only [← bimoduleTensorMap_comp, Category.id_comp, Category.comp_id] }
  map_id M := by
    apply NatTrans.ext
    funext N
    exact bimoduleTensorMap_id Γ Δ Θ
  map_comp f f' := by
    apply NatTrans.ext
    funext N
    -- Compute composition componentwise in the functor category.
    change bimoduleTensorMap Γ Δ Θ (f ≫ f') (𝟙 N) =
      bimoduleTensorMap Γ Δ Θ f (𝟙 N) ≫ bimoduleTensorMap Γ Δ Θ f' (𝟙 N)
    rw [← bimoduleTensorMap_comp, Category.id_comp]

@[simp]
theorem bimoduleTensor_obj_obj : ((bimoduleTensor Γ Δ Θ).obj M).obj N =
    bimoduleTensorObj Γ Δ Θ M N := rfl

@[simp]
theorem bimoduleTensor_obj_map (g : N ⟶ N') :
    ((bimoduleTensor Γ Δ Θ).obj M).map g = bimoduleTensorMap Γ Δ Θ (𝟙 M) g := rfl

@[simp]
theorem bimoduleTensor_map_app (f : M ⟶ M') :
    ((bimoduleTensor Γ Δ Θ).map f).app N = bimoduleTensorMap Γ Δ Θ f (𝟙 N) := rfl

instance : ((bimoduleTensor Γ Δ Θ).obj M).Additive where
  map_add := bimoduleTensorMap_add_right Γ Δ Θ (𝟙 M) _ _

instance : ((bimoduleTensor Γ Δ Θ).flip.obj N).Additive where
  map_add := bimoduleTensorMap_add_left Γ Δ Θ _ _ (𝟙 N)

instance : (bimoduleTensor Γ Δ Θ).Additive where
  map_add {X Y f g} := by
    apply NatTrans.ext
    funext N
    exact bimoduleTensorMap_add_left Γ Δ Θ f g (𝟙 N)

instance : (bimoduleTensor Γ Δ Θ).flip.Additive where
  map_add {X Y f g} := by
    apply NatTrans.ext
    funext M
    exact bimoduleTensorMap_add_right Γ Δ Θ (𝟙 M) f g

instance : ((bimoduleTensor Γ Δ Θ).obj M).Linear k where
  map_smul f c := bimoduleTensorMap_smul_right Γ Δ Θ c (𝟙 M) f

instance : ((bimoduleTensor Γ Δ Θ).flip.obj N).Linear k where
  map_smul f c := bimoduleTensorMap_smul_left Γ Δ Θ c f (𝟙 N)

instance : (bimoduleTensor Γ Δ Θ).Linear k where
  map_smul f c := by
    apply NatTrans.ext
    funext N
    exact bimoduleTensorMap_smul_left Γ Δ Θ c f (𝟙 N)

instance : (bimoduleTensor Γ Δ Θ).flip.Linear k where
  map_smul f c := by
    apply NatTrans.ext
    funext M
    exact bimoduleTensorMap_smul_right Γ Δ Θ c (𝟙 M) f

end Tensor

end TauCeti.GradedModuleCat
