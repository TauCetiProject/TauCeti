/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.TransferInstance
public import TauCeti.Algebra.Homology.DG.Bimodule.Defs
public import TauCeti.Algebra.Homology.DG.Module.Right.Hom.Complex
public import TauCeti.Algebra.Homology.DG.Module.Right.Yoneda

/-!
# The internal Hom of differential graded modules

Let `M` be a differential graded `(A, B)`-bimodule and `N` a differential graded right
`B`-module.  The **internal Hom** `Hom_B(M, N)` consists of the finite sums of homogeneous
right `B`-module maps `M ⟶ N`; its degree-`p` piece is the module of right `B`-module maps
raising degree by `p`, the degree-`p` term of the Hom complex.  The left `A`-action on `M`
makes it a right `A`-module,

`(f · a)(x) = f (a x)`,

and the graded commutator `δ f = d_N ∘ f - (-1) ^ p f ∘ d_M` on maps of degree `p` makes it a
differential graded right `A`-module.  No sign enters the action, because in `f (a x)` the
scalar `a` is moved past neither `f` nor `x`.  The Leibniz rule
`δ (f · a) = δ f · a + (-1) ^ |f| f · d a` comes from the left Leibniz rule of `M`.

The internal Hom is the right adjoint of tensoring with `M`; this file constructs the internal Hom
and its DG right module structure, not the adjunction.  The regular bimodule represents the
identity: evaluation at the unit is a bijective morphism of DG right modules `Hom_B(B, N) ⟶ N`.

## Main definitions

* `TauCeti.DGRightModule.InternalHom`: the carrier of the internal Hom, the finite sums of
  homogeneous right-module maps, with its right action of `A`.
* `TauCeti.DGRightModule.InternalHom.grading`: its grading by the degree of a map.
* `TauCeti.DGRightModule.InternalHom.differential`: the graded commutator with the two module
  differentials.
* `TauCeti.DGRightModule.InternalHom.evalOne`: evaluation at the unit, from the internal Hom out
  of the regular bimodule.
* `TauCeti.DGRightModule.InternalHom.rightMul`: right multiplication by an element of `N`, the
  inverse of evaluation at the unit.

## Main results

* `TauCeti.DGRightModule.InternalHom.isInternal_grading`: every element of the internal Hom is
  uniquely a finite sum of homogeneous maps.
* `TauCeti.IsDGBimodule.internalHom`: the internal Hom out of a DG `(A, B)`-bimodule into a DG
  right `B`-module is a DG right `A`-module.
* `TauCeti.DGRightModule.InternalHom.evalOne_bijective`: `Hom_B(B, N) ⟶ N` is bijective.

## References

* B. Keller, *Deriving DG categories*, Sections 1.1, 2 and 6.1.
-/

public section

open DirectSum MulOpposite

namespace TauCeti

universe uR uA uB uM uN

section Precomposition

variable {R : Type uR} {A : Type uA} {B : Type uB} {M : Type uM} {N : Type uN}
  [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
  [AddCommGroup M] [Module R M] [Module Bᵐᵒᵖ M] [IsScalarTower R Bᵐᵒᵖ M]
  [AddCommGroup N] [Module R N] [Module Bᵐᵒᵖ N] [IsScalarTower R Bᵐᵒᵖ N]
  [Module A M] [SMulCommClass A Bᵐᵒᵖ M]
  {𝒜 : ℤ → Submodule R A} {ℳ : ℤ → Submodule R M} [SetLike.GradedSMul 𝒜 ℳ]
  {𝒩 : ℤ → Submodule R N}

/-- Precomposing a right-module map of degree `p` with the action of an element of degree `q`
gives a right-module map of degree `q + p`. -/
theorem comp_toLinearMap_mem_dgRightModuleCochains {p q : ℤ} {f : M →ₗ[Bᵐᵒᵖ] N}
    (hf : f ∈ dgRightModuleCochains (R := R) (A := B) (ℳ := ℳ) (ℳN := 𝒩) p) {a : A}
    (ha : a ∈ 𝒜 q) :
    f ∘ₗ DistribSMul.toLinearMap Bᵐᵒᵖ M a ∈
      dgRightModuleCochains (R := R) (A := B) (ℳ := ℳ) (ℳN := 𝒩) (q + p) := by
  refine dgRightModuleCochains.mem_iff.2 (LinearMap.isHomogeneous_def.2 fun r x hx ↦ ?_)
  have h := (dgRightModuleCochains.mem_iff.1 hf).map_mem (SetLike.GradedSMul.smul_mem ha hx)
  rw [vadd_eq_add] at h
  rwa [show r + (q + p) = q + r + p by abel]

variable (𝒜) [DirectSum.Decomposition 𝒜] in
include 𝒜 in
/-- Precomposing a finite sum of homogeneous right-module maps with the action of an element of
`A` gives a finite sum of homogeneous right-module maps. -/
theorem comp_toLinearMap_mem_iSup_dgRightModuleCochains {f : M →ₗ[Bᵐᵒᵖ] N}
    (hf : f ∈ ⨆ p, dgRightModuleCochains (R := R) (A := B) (ℳ := ℳ) (ℳN := 𝒩) p) (a : A) :
    f ∘ₗ DistribSMul.toLinearMap Bᵐᵒᵖ M a ∈
      ⨆ p, dgRightModuleCochains (R := R) (A := B) (ℳ := ℳ) (ℳN := 𝒩) p := by
  refine Submodule.iSup_induction _ (motive := fun f ↦ f ∘ₗ DistribSMul.toLinearMap Bᵐᵒᵖ M a ∈
      ⨆ p, dgRightModuleCochains (R := R) (A := B) (ℳ := ℳ) (ℳN := 𝒩) p) hf
    (fun p f hf ↦ ?_) (by rw [LinearMap.zero_comp]; exact zero_mem _)
    (fun f g hf hg ↦ by rw [LinearMap.add_comp]; exact add_mem hf hg)
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero =>
    convert zero_mem (⨆ p, dgRightModuleCochains (R := R) (A := B) (ℳ := ℳ) (ℳN := 𝒩) p)
    ext x
    simp
  | @homogeneous q a =>
    exact Submodule.mem_iSup_of_mem (q + p)
      (comp_toLinearMap_mem_dgRightModuleCochains hf a.2)
  | add a a' ha ha' =>
    convert add_mem ha ha' using 1
    ext x
    simp [add_smul]

end Precomposition

namespace DGRightModule

/-- The carrier of the **internal Hom** `Hom_B(M, N)`: the finite sums of homogeneous right
`B`-module maps `M ⟶ N`, the sum over all degrees `p` of the right-module maps raising degree by
`p`.

The grading `_𝒜` of the algebra acting on `M` from the left does not enter the elements.  It
records that algebra, so that the right action of `A` defined by `(f · a)(x) = f (a x)` is an
instance on the carrier. -/
structure InternalHom {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
    (_𝒜 : ℤ → Submodule R A) (B : Type uB) [Ring B] [Algebra R B]
    {M : Type uM} {N : Type uN}
    [AddCommGroup M] [Module R M] [Module Bᵐᵒᵖ M] [IsScalarTower R Bᵐᵒᵖ M]
    [AddCommGroup N] [Module R N] [Module Bᵐᵒᵖ N] [IsScalarTower R Bᵐᵒᵖ N]
    (ℳ : ℤ → Submodule R M) [DirectSum.Decomposition ℳ]
    (𝒩 : ℤ → Submodule R N) [DirectSum.Decomposition 𝒩] where
  /-- The underlying finite sum of homogeneous right-module maps. -/
  val : ↥(⨆ p, dgRightModuleCochains (R := R) (A := B) (ℳ := ℳ) (ℳN := 𝒩) p)

namespace InternalHom

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A] {𝒜 : ℤ → Submodule R A}
  {B : Type uB} {M : Type uM} {N : Type uN} [Ring B] [Algebra R B]
  [AddCommGroup M] [Module R M] [Module Bᵐᵒᵖ M] [IsScalarTower R Bᵐᵒᵖ M]
  [AddCommGroup N] [Module R N] [Module Bᵐᵒᵖ N] [IsScalarTower R Bᵐᵒᵖ N]
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  {𝒩 : ℤ → Submodule R N} [DirectSum.Decomposition 𝒩]

/-! ### The module structure over the ground ring -/

instance : AddCommGroup (InternalHom 𝒜 B ℳ 𝒩) :=
  Equiv.addCommGroup { toFun := val, invFun := mk, left_inv _ := rfl, right_inv _ := rfl }

instance : Module R (InternalHom 𝒜 B ℳ 𝒩) :=
  AddEquiv.module R
    { toFun := val, invFun := mk, left_inv _ := rfl, right_inv _ := rfl, map_add' _ _ := rfl }

/-- The underlying right-module map, as an `R`-linear map out of the internal Hom. -/
def coeLM : InternalHom 𝒜 B ℳ 𝒩 →ₗ[R] M →ₗ[Bᵐᵒᵖ] N where
  toFun f := f.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance : FunLike (InternalHom 𝒜 B ℳ 𝒩) M N where
  coe f := (coeLM f : M →ₗ[Bᵐᵒᵖ] N)
  coe_injective f g h := by
    obtain ⟨⟨f, hf⟩⟩ := f
    obtain ⟨⟨g, hg⟩⟩ := g
    congr
    exact LinearMap.ext (congrFun h)

@[simp]
theorem coeLM_apply (f : InternalHom 𝒜 B ℳ 𝒩) (x : M) : coeLM f x = f x := (rfl)

@[simp]
theorem mk_apply (f : ↥(⨆ p, dgRightModuleCochains (R := R) (A := B) (ℳ := ℳ) (ℳN := 𝒩) p))
    (x : M) : (mk f : InternalHom 𝒜 B ℳ 𝒩) x = (f : M →ₗ[Bᵐᵒᵖ] N) x := (rfl)

/-- Elements of the internal Hom are equal when they agree as maps. -/
@[ext]
theorem ext {f g : InternalHom 𝒜 B ℳ 𝒩} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.coe_injective (funext h)

/-- The map underlying an element of the internal Hom is injective in the element. -/
theorem coeLM_injective :
    Function.Injective (coeLM (𝒜 := 𝒜) (B := B) (ℳ := ℳ) (𝒩 := 𝒩)) :=
  fun _ _ h ↦ ext fun x ↦ LinearMap.congr_fun h x

@[simp]
theorem zero_apply (x : M) : (0 : InternalHom 𝒜 B ℳ 𝒩) x = 0 := (rfl)

@[simp]
theorem add_apply (f g : InternalHom 𝒜 B ℳ 𝒩) (x : M) : (f + g) x = f x + g x := (rfl)

@[simp]
theorem sub_apply (f g : InternalHom 𝒜 B ℳ 𝒩) (x : M) : (f - g) x = f x - g x := (rfl)

@[simp]
theorem neg_apply (f : InternalHom 𝒜 B ℳ 𝒩) (x : M) : (-f) x = -f x := (rfl)

@[simp]
theorem smul_apply (r : R) (f : InternalHom 𝒜 B ℳ 𝒩) (x : M) : (r • f) x = r • f x := (rfl)

@[simp]
theorem zsmul_apply (n : ℤ) (f : InternalHom 𝒜 B ℳ 𝒩) (x : M) : (n • f) x = n • f x := (rfl)

/-- Every element of the internal Hom is a right-module map. -/
instance : LinearMapClass (InternalHom 𝒜 B ℳ 𝒩) Bᵐᵒᵖ M N where
  map_add f := (coeLM f).map_add
  map_smulₛₗ f := (coeLM f).map_smul

/-! ### The grading -/

variable (𝒜 B ℳ 𝒩) in
/-- The **grading of the internal Hom**: its degree-`p` piece consists of the right-module maps
raising degree by `p`. -/
def grading (p : ℤ) : Submodule R (InternalHom 𝒜 B ℳ 𝒩) :=
  (dgRightModuleCochains (R := R) (A := B) (ℳ := ℳ) (ℳN := 𝒩) p).comap coeLM

@[simp]
theorem mem_grading_iff {p : ℤ} {f : InternalHom 𝒜 B ℳ 𝒩} :
    f ∈ grading 𝒜 B ℳ 𝒩 p ↔
      coeLM f ∈ dgRightModuleCochains (R := R) (A := B) (ℳ := ℳ) (ℳN := 𝒩) p :=
  Iff.rfl

/-- An element of degree `p` of the internal Hom sends elements of degree `q` to elements of degree
`q + p`. -/
theorem map_mem_of_mem_grading {p q : ℤ} {f : InternalHom 𝒜 B ℳ 𝒩} (hf : f ∈ grading 𝒜 B ℳ 𝒩 p)
    {x : M} (hx : x ∈ ℳ q) : f x ∈ 𝒩 (q + p) :=
  (dgRightModuleCochains.mem_iff.1 (mem_grading_iff.1 hf)).map_mem hx

variable (𝒜) in
/-- A right-module map of degree `p`, as an element of the internal Hom. -/
def ofCochains (p : ℤ) :
    dgRightModuleCochains (R := R) (A := B) (ℳ := ℳ) (ℳN := 𝒩) p →ₗ[R] InternalHom 𝒜 B ℳ 𝒩 where
  toFun f := ⟨⟨f.1, Submodule.mem_iSup_of_mem p f.2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem ofCochains_apply (p : ℤ)
    (f : dgRightModuleCochains (R := R) (A := B) (ℳ := ℳ) (ℳN := 𝒩) p) (x : M) :
    ofCochains 𝒜 p f x = (f : M →ₗ[Bᵐᵒᵖ] N) x := (rfl)

@[simp]
theorem coeLM_ofCochains (p : ℤ)
    (f : dgRightModuleCochains (R := R) (A := B) (ℳ := ℳ) (ℳN := 𝒩) p) :
    coeLM (ofCochains 𝒜 p f) = f := (rfl)

/-- A right-module map of degree `p` lies in the degree-`p` piece of the internal Hom. -/
theorem ofCochains_mem_grading (p : ℤ)
    (f : dgRightModuleCochains (R := R) (A := B) (ℳ := ℳ) (ℳN := 𝒩) p) :
    ofCochains 𝒜 p f ∈ grading 𝒜 B ℳ 𝒩 p :=
  f.2

/-- The elements of degree `p` of the internal Hom are exactly the right-module maps of degree
`p`. -/
theorem mem_grading_iff_exists {p : ℤ} {f : InternalHom 𝒜 B ℳ 𝒩} :
    f ∈ grading 𝒜 B ℳ 𝒩 p ↔ ∃ g, ofCochains 𝒜 p g = f :=
  ⟨fun hf ↦ ⟨⟨coeLM f, hf⟩, coeLM_injective rfl⟩, fun ⟨g, hg⟩ ↦ hg ▸ ofCochains_mem_grading p g⟩

variable (𝒜 B ℳ 𝒩) in
/-- The grading of the internal Hom is a direct-sum decomposition: every element is uniquely a
finite sum of homogeneous right-module maps. -/
theorem isInternal_grading : DirectSum.IsInternal (grading 𝒜 B ℳ 𝒩) := by
  refine (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2 ⟨?_, ?_⟩
  · refine (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).2 fun s v hv hsum i hi ↦ ?_
    refine coeLM_injective ?_
    rw [map_zero]
    refine (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).1 iSupIndep_dgRightModuleCochains s
      (fun j ↦ coeLM (v j)) (fun j hj ↦ hv j hj) ?_ i hi
    rw [← map_sum, hsum, map_zero]
  · refine eq_top_iff.2 fun f _ ↦ ?_
    obtain ⟨f', hf', hff'⟩ : ∃ f' ∈ ⨆ p, grading 𝒜 B ℳ 𝒩 p, coeLM f' = coeLM f := by
      refine Submodule.iSup_induction _ (motive := fun g ↦ ∃ f' ∈ ⨆ p, grading 𝒜 B ℳ 𝒩 p,
        coeLM f' = g) f.val.2 (fun p g hg ↦ ?_) ⟨0, zero_mem _, map_zero _⟩ ?_
      · exact ⟨ofCochains 𝒜 p ⟨g, hg⟩, Submodule.mem_iSup_of_mem p (ofCochains_mem_grading p _),
          rfl⟩
      · rintro _ _ ⟨f₁, hf₁, rfl⟩ ⟨f₂, hf₂, rfl⟩
        exact ⟨f₁ + f₂, add_mem hf₁ hf₂, map_add _ _ _⟩
    rwa [← coeLM_injective hff']

/-- The decomposition of the internal Hom into homogeneous right-module maps. -/
noncomputable instance : DirectSum.Decomposition (grading 𝒜 B ℳ 𝒩) :=
  (isInternal_grading 𝒜 B ℳ 𝒩).chooseDecomposition

/-! ### The differential -/

section Differential

variable {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {dB : B →ₗ[R] B} {hB : IsDGAlgebra ℬ dB}
  [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece 𝒩]
  {dM : M →ₗ[R] M} {dN : N →ₗ[R] N}

variable (𝒜) in
/-- The **differential of the internal Hom**: on a right-module map `f` of degree `p` it is the
graded commutator `d_N ∘ f - (-1) ^ p f ∘ d_M`, the differential of the Hom complex, and it is
extended additively to finite sums of homogeneous maps. -/
noncomputable def differential (hM : IsDGRightModule hB ℳ dM) (hN : IsDGRightModule hB 𝒩 dN) :
    InternalHom 𝒜 B ℳ 𝒩 →ₗ[R] InternalHom 𝒜 B ℳ 𝒩 :=
  (DirectSum.toModule R ℤ _ fun p ↦
    ofCochains 𝒜 (p + 1) ∘ₗ dgRightModuleCochains.differential (hM := hM) (hN := hN) p ∘ₗ
      (coeLM ∘ₗ (grading 𝒜 B ℳ 𝒩 p).subtype).codRestrict _ fun f ↦ f.2) ∘ₗ
    (decomposeLinearEquiv (grading 𝒜 B ℳ 𝒩)).toLinearMap

variable (hM : IsDGRightModule hB ℳ dM) (hN : IsDGRightModule hB 𝒩 dN)

/-- On a right-module map of degree `p`, the differential of the internal Hom is the differential
of the Hom complex. -/
@[simp]
theorem differential_ofCochains (p : ℤ)
    (f : dgRightModuleCochains (R := R) (A := B) (ℳ := ℳ) (ℳN := 𝒩) p) :
    differential 𝒜 hM hN (ofCochains 𝒜 p f) =
      ofCochains 𝒜 (p + 1) (dgRightModuleCochains.differential (hM := hM) (hN := hN) p f) := by
  have h : decomposeLinearEquiv (grading 𝒜 B ℳ 𝒩) (ofCochains 𝒜 p f) =
      lof R ℤ (fun q ↦ grading 𝒜 B ℳ 𝒩 q) p ⟨ofCochains 𝒜 p f, ofCochains_mem_grading p f⟩ :=
    decomposeLinearEquiv_apply_coe _ p ⟨_, ofCochains_mem_grading p f⟩
  have hf : (coeLM ∘ₗ (grading 𝒜 B ℳ 𝒩 p).subtype).codRestrict _ (fun g ↦ g.2)
      ⟨ofCochains 𝒜 p f, ofCochains_mem_grading p f⟩ = f :=
    Subtype.ext ((LinearMap.codRestrict_apply _ _ _).trans (coeLM_ofCochains (𝒜 := 𝒜) p f))
  rw [differential, LinearMap.comp_apply, LinearEquiv.coe_coe, h, DirectSum.toModule_lof,
    LinearMap.comp_apply, LinearMap.comp_apply, hf]

/-- The differential of the internal Hom on a homogeneous map `f` of degree `p` is the graded
commutator `d_N ∘ f - (-1) ^ p f ∘ d_M`. -/
theorem differential_apply_of_mem {p : ℤ} {f : InternalHom 𝒜 B ℳ 𝒩}
    (hf : f ∈ grading 𝒜 B ℳ 𝒩 p) (x : M) :
    differential 𝒜 hM hN f x = dN (f x) - p.negOnePow • f (dM x) := by
  obtain ⟨g, rfl⟩ := mem_grading_iff_exists.1 hf
  rw [differential_ofCochains, ofCochains_apply, dgRightModuleCochains.differential_apply,
    ofCochains_apply, ofCochains_apply]

/-- The differential of the internal Hom raises degree by one. -/
theorem differential_mem_grading {p : ℤ} {f : InternalHom 𝒜 B ℳ 𝒩}
    (hf : f ∈ grading 𝒜 B ℳ 𝒩 p) : differential 𝒜 hM hN f ∈ grading 𝒜 B ℳ 𝒩 (p + 1) := by
  obtain ⟨g, rfl⟩ := mem_grading_iff_exists.1 hf
  rw [differential_ofCochains]
  exact ofCochains_mem_grading _ _

/-- The differential of the internal Hom squares to zero. -/
@[simp]
theorem differential_sq_zero (f : InternalHom 𝒜 B ℳ 𝒩) :
    differential 𝒜 hM hN (differential 𝒜 hM hN f) = 0 := by
  induction f using DirectSum.Decomposition.inductionOn (grading 𝒜 B ℳ 𝒩) with
  | zero => rw [map_zero, map_zero]
  | @homogeneous p f =>
    obtain ⟨g, hg⟩ := mem_grading_iff_exists.1 f.2
    rw [← hg, differential_ofCochains, differential_ofCochains,
      ← LinearMap.comp_apply (dgRightModuleCochains.differential (p + 1)),
      dgRightModuleCochains.differential_comp_self, LinearMap.zero_apply, map_zero]
  | add f g hf hg => rw [map_add, map_add, hf, hg, add_zero]

end Differential

/-! ### The right action of the algebra acting on the left of `M` -/

section Action

variable [Module A M] [SMulCommClass A Bᵐᵒᵖ M] [DirectSum.Decomposition 𝒜]
  [SetLike.GradedSMul 𝒜 ℳ]

/-- The right action of `A` on the internal Hom, `(f · a)(x) = f (a x)`. -/
instance : SMul Aᵐᵒᵖ (InternalHom 𝒜 B ℳ 𝒩) where
  smul a f := ⟨⟨(f.val : M →ₗ[Bᵐᵒᵖ] N) ∘ₗ DistribSMul.toLinearMap Bᵐᵒᵖ M a.unop,
    comp_toLinearMap_mem_iSup_dgRightModuleCochains 𝒜 f.val.2 a.unop⟩⟩

/-- The right action of `A` on the internal Hom precomposes with the left action on `M`. -/
@[simp]
theorem op_smul_apply (a : Aᵐᵒᵖ) (f : InternalHom 𝒜 B ℳ 𝒩) (x : M) :
    (a • f) x = f (a.unop • x) := (rfl)

instance : Module Aᵐᵒᵖ (InternalHom 𝒜 B ℳ 𝒩) where
  one_smul f := ext fun x ↦ by simp
  mul_smul a b f := ext fun x ↦ by simp [mul_smul]
  smul_zero a := ext fun x ↦ by simp
  smul_add a f g := ext fun x ↦ by simp
  add_smul a b f := ext fun x ↦ by simp [add_smul]
  zero_smul f := ext fun x ↦ by simp

instance [IsScalarTower R A M] : IsScalarTower R Aᵐᵒᵖ (InternalHom 𝒜 B ℳ 𝒩) where
  smul_assoc r a f := ext fun x ↦ by
    simp only [op_smul_apply, smul_apply, unop_smul, smul_assoc]
    exact (coeLM f).map_smul_of_tower r _

/-- The right action of `A` adds degrees: a homogeneous map of degree `p` acted on by an element of
degree `q` has degree `q + p`. -/
theorem op_smul_mem_grading {p q : ℤ} {a : A} (ha : a ∈ 𝒜 q) {f : InternalHom 𝒜 B ℳ 𝒩}
    (hf : f ∈ grading 𝒜 B ℳ 𝒩 p) : op a • f ∈ grading 𝒜 B ℳ 𝒩 (q + p) :=
  comp_toLinearMap_mem_dgRightModuleCochains (mem_grading_iff.1 hf) ha

instance : SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece
    (grading 𝒜 B ℳ 𝒩) where
  smul_mem {q p a f} ha hf := by
    rw [InternalGrading.mem_opposite_piece_iff, InternalGrading.ofDecomposition_piece] at ha
    exact op_smul_mem_grading ha hf

end Action

end InternalHom

end DGRightModule

namespace IsDGBimodule

open DGRightModule

variable {R : Type uR} {A : Type uA} {B : Type uB} {M : Type uM} {N : Type uN}
  [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
  [AddCommGroup M] [Module R M] [Module A M] [Module Bᵐᵒᵖ M]
  [IsScalarTower R A M] [IsScalarTower R Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]
  [AddCommGroup N] [Module R N] [Module Bᵐᵒᵖ N] [IsScalarTower R Bᵐᵒᵖ N]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B} [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B} {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB}
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece ℳ]
  {𝒩 : ℤ → Submodule R N} [DirectSum.Decomposition 𝒩]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece 𝒩]
  {dM : M →ₗ[R] M} {dN : N →ₗ[R] N}

/-- **The internal Hom is a differential graded right module.**  For a DG `(A, B)`-bimodule `M`
and a DG right `B`-module `N`, the finite sums of homogeneous right `B`-module maps `M ⟶ N`, with
the action `(f · a)(x) = f (a x)` and the graded commutator `d_N ∘ f - (-1) ^ |f| f ∘ d_M`, form a
DG right `A`-module. -/
theorem internalHom (hM : IsDGBimodule hA hB ℳ dM) (hN : IsDGRightModule hB 𝒩 dN) :
    IsDGRightModule hA (InternalHom.grading 𝒜 B ℳ 𝒩)
      (InternalHom.differential 𝒜 hM.isDGRightModule hN) where
  isHomogeneous := LinearMap.isHomogeneous_def.2 fun _ _ hf ↦
    InternalHom.differential_mem_grading _ _ hf
  sq_zero := InternalHom.differential_sq_zero _ _
  leibniz {q f} hf a := by
    induction a using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | @homogeneous r a =>
      obtain ⟨a, ha⟩ := a
      ext x
      simp only [InternalHom.add_apply,
        InternalHom.differential_apply_of_mem _ _ (InternalHom.op_smul_mem_grading ha hf),
        InternalHom.op_smul_apply, unop_op, InternalHom.differential_apply_of_mem _ _ hf,
        hM.leibniz ha x, map_add, Units.smul_def, map_zsmul, InternalHom.zsmul_apply,
        Int.negOnePow_add, mul_smul]
      module
    | add a a' ha ha' =>
      simp only [op_add, add_smul, map_add, ha, ha', smul_add]
      abel

end IsDGBimodule

/-! ### The internal Hom out of the regular bimodule -/

namespace DGRightModule.InternalHom

variable {R : Type uR} {B : Type uB} {N : Type uN} [CommRing R] [Ring B] [Algebra R B]
  [AddCommGroup N] [Module R N] [Module Bᵐᵒᵖ N] [IsScalarTower R Bᵐᵒᵖ N]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {dB : B →ₗ[R] B} {hB : IsDGAlgebra ℬ dB}
  {𝒩 : ℤ → Submodule R N} [DirectSum.Decomposition 𝒩]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece 𝒩]
  {dN : N →ₗ[R] N}

variable (ℬ 𝒩) in
/-- **Right multiplication** `b ↦ n b` by an element `n` of `N`, as an element of the internal Hom
out of the regular bimodule.  On each homogeneous component of `n` it is the inverse of the
degreewise Yoneda lemma `TauCeti.dgYonedaCochainEquiv`, and it is inverse to evaluation at the
unit. -/
noncomputable def rightMul : N →ₗ[R] InternalHom ℬ B ℬ 𝒩 :=
  DirectSum.toModule R ℤ _ (fun q ↦ ofCochains ℬ q ∘ₗ
    (dgYonedaCochainEquiv (𝒜 := ℬ) (ℳ := 𝒩) q).symm.toLinearMap) ∘ₗ
    (decomposeLinearEquiv 𝒩).toLinearMap

/-- On an element of degree `q`, right multiplication is the inverse of the degreewise Yoneda
lemma. -/
theorem rightMul_coe {q : ℤ} (n : 𝒩 q) :
    rightMul ℬ 𝒩 (n : N) = ofCochains ℬ q ((dgYonedaCochainEquiv (𝒜 := ℬ) (ℳ := 𝒩) q).symm n) := by
  rw [rightMul, LinearMap.comp_apply, LinearEquiv.coe_coe, decomposeLinearEquiv_apply_coe,
    DirectSum.toModule_lof, LinearMap.comp_apply, LinearEquiv.coe_coe]

@[simp]
theorem rightMul_apply (n : N) (b : B) : rightMul ℬ 𝒩 n b = op b • n := by
  induction n using DirectSum.Decomposition.inductionOn 𝒩 with
  | zero => rw [map_zero, zero_apply, smul_zero]
  | @homogeneous q n => rw [rightMul_coe, ofCochains_apply, dgYonedaCochainEquiv_symm_apply]
  | add n n' hn hn' => rw [map_add, add_apply, hn, hn', smul_add]

variable (hN : IsDGRightModule hB 𝒩 dN)

/-- **Evaluation at the unit**, from the internal Hom out of the regular bimodule `B` to `N`, as a
morphism of DG right `B`-modules. -/
def evalOne : DGRightModuleHom (hB.isDGBimodule.internalHom hN) hN where
  toFun f := f 1
  map_add' f g := add_apply f g 1
  map_smul' b f := by
    rw [op_smul_apply, RingHom.id_apply, ← map_smul, smul_eq_mul, mul_one, smul_eq_mul_unop,
      one_mul]
  map_mem' {q f} hf := by
    simpa only [zero_add, LinearMap.coe_mk, AddHom.coe_mk] using
      map_mem_of_mem_grading hf (SetLike.GradedOne.one_mem (A := ℬ))
  map_d' f := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    induction f using DirectSum.Decomposition.inductionOn (grading ℬ B ℬ 𝒩) with
    | zero => rw [zero_apply, map_zero, map_zero, zero_apply]
    | @homogeneous q f =>
      rw [differential_apply_of_mem _ _ f.2, hB.map_one_eq_zero, map_zero, smul_zero, sub_zero]
    | add f g hf hg => rw [add_apply, map_add, map_add, add_apply, hf, hg]

@[simp]
theorem evalOne_apply (f : InternalHom ℬ B ℬ 𝒩) : evalOne hN f = f 1 := (rfl)

/-- Evaluation at the unit is a left inverse of right multiplication. -/
theorem evalOne_rightMul (n : N) : evalOne hN (rightMul ℬ 𝒩 n) = n := by
  rw [evalOne_apply, rightMul_apply, op_one, one_smul]

/-- Right multiplication is a left inverse of evaluation at the unit. -/
theorem rightMul_evalOne (f : InternalHom ℬ B ℬ 𝒩) : rightMul ℬ 𝒩 (evalOne hN f) = f := by
  induction f using DirectSum.Decomposition.inductionOn (grading ℬ B ℬ 𝒩) with
  | zero => rw [map_zero, map_zero]
  | @homogeneous q f =>
    obtain ⟨g, hg⟩ := mem_grading_iff_exists.1 f.2
    rw [← hg, evalOne_apply, ofCochains_apply, ← dgYonedaCochainEquiv_apply, rightMul_coe,
      LinearEquiv.symm_apply_apply]
  | add f g hf hg => rw [map_add, map_add, hf, hg]

/-- **The regular bimodule represents the identity**: evaluation at the unit is a bijection
`Hom_B(B, N) ⟶ N`, with inverse `rightMul` sending `n` to right multiplication `b ↦ n b`. -/
theorem evalOne_bijective : Function.Bijective (evalOne hN) :=
  ⟨Function.LeftInverse.injective (g := rightMul ℬ 𝒩) (rightMul_evalOne hN),
    Function.RightInverse.surjective (evalOne_rightMul hN)⟩

end DGRightModule.InternalHom

end TauCeti
