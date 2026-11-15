/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.VectorField.LieBracket
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Module
public import TauCeti.Geometry.Manifold.VectorBundle.Trivial
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Geometry.Manifold.VectorBundle.Section.Map
import TauCeti.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Sections of trivial vector bundles

A `C^n` section of `Bundle.Trivial M F` with normed fibre `F` is a `C^n` map `M → F`
(`ContMDiffSection.trivialEquiv`). When the fibre `W` is instead a finite-dimensional Hausdorff
topological module without a fixed norm (such as a real `LieAlgebra` or `GroupLieAlgebra J G`),
`Bundle.TrivialModel 𝕜 W` (from `TauCeti.Geometry.Manifold.VectorBundle.Trivial`) supplies
`Fin (Module.finrank 𝕜 W) → 𝕜` as a nominal model fibre without `AddCommGroup` diamonds on `W`, and
`ContMDiffSection.modelDeriv` differentiates smooth sections along tangent vectors independently of
any norm on `W`.

## Main definitions

* `ContMDiffSection.trivialEquiv`, `ContMDiffSection.trivialConst`, `ContMDiffSection.trivialCoord`:
  function equivalence, constant sections, and basis coordinates for `Bundle.Trivial M F`.
* `ContMDiffSection.modelEquiv`, `ContMDiffSection.modelConst`, `ContMDiffSection.modelCoord`,
  `ContMDiffSection.modelMap`, `ContMDiffSection.modelPullback`, `ContMDiffSection.modelDeriv`,
  `ContMDiffSection.modelLieDeriv`: section operations and norm-independent derivatives on
  `Bundle.Trivial M W`.
-/

public section

noncomputable section

open Bundle Manifold Set VectorField
open scoped Manifold ContDiff

namespace ContMDiffSection

variable {𝕜 E H : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ∞ω}

/-- The `C^n⟮I, M; 𝕜⟯`-linear equivalence between `C^n` sections of `Bundle.Trivial M F` and `C^n`
maps `M → F`. -/
def trivialEquiv : Cₛ^n⟮I; F, Bundle.Trivial M F⟯ ≃ₗ[C^n⟮I, M; 𝕜⟯] C^n⟮I, M; 𝓘(𝕜, F), F⟯ where
  toFun s := ⟨fun x ↦ s x, (Bundle.Trivial.contMDiff_mk_iff.1 s.contMDiff).2⟩
  invFun f := ⟨fun x ↦ f x, Bundle.Trivial.contMDiff_mk_iff.2 ⟨contMDiff_id, f.contMDiff⟩⟩
  left_inv _ := by ext x; rfl
  right_inv _ := by ext x; rfl
  map_add' _ _ := by ext x; rfl
  map_smul' f s := ContMDiffMap.ext fun x ↦ ContMDiffSection.smul_apply f s x

@[simp] theorem trivialEquiv_apply (s : Cₛ^n⟮I; F, Bundle.Trivial M F⟯) (x : M) :
    trivialEquiv s x = s x := (rfl)

@[simp] theorem coe_trivialEquiv (s : Cₛ^n⟮I; F, Bundle.Trivial M F⟯) :
    ⇑(trivialEquiv s : C^n⟮I, M; 𝓘(𝕜, F), F⟯) = ⇑s := (rfl)

@[simp] theorem trivialEquiv_symm_apply (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) (x : M) :
    trivialEquiv.symm f x = f x := (rfl)

@[simp] theorem coe_trivialEquiv_symm (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) :
    ⇑(trivialEquiv.symm f : Cₛ^n⟮I; F, Bundle.Trivial M F⟯) = ⇑f := (rfl)

variable (I M n) in
/-- Constant `C^n` sections of `Bundle.Trivial M F`, as a `𝕜`-linear map from `F`. -/
def trivialConst : F →ₗ[𝕜] Cₛ^n⟮I; F, Bundle.Trivial M F⟯ where
  toFun v := trivialEquiv.symm (ContMDiffMap.const v)
  map_add' _ _ := by ext x; rfl
  map_smul' _ _ := by ext x; rfl

@[simp] theorem trivialConst_apply (v : F) (x : M) : trivialConst I M n v x = v := (rfl)

@[simp] theorem coe_trivialConst (v : F) : ⇑(trivialConst I M n v) = Function.const M v := (rfl)

@[simp] theorem trivialEquiv_trivialConst (v : F) :
    trivialEquiv (trivialConst I M n v) = ContMDiffMap.const v := (rfl)

/-- Over a nonempty base, constant sections of a trivial bundle determine their fibre value. -/
theorem trivialConst_injective [Nonempty M] :
    Function.Injective (trivialConst I M n (F := F)) := fun _ _ h ↦ by
  obtain ⟨x₀⟩ := ‹Nonempty M›; simpa using congr($h x₀)

section Basis

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] {ι : Type*}

/-- The `i`-th coordinate of a `C^n` section of `Bundle.Trivial M F` in a basis `b` of `F`. -/
def trivialCoord (b : Module.Basis ι 𝕜 F) (i : ι) :
    Cₛ^n⟮I; F, Bundle.Trivial M F⟯ →ₗ[C^n⟮I, M; 𝕜⟯] C^n⟮I, M; 𝕜⟯ where
  toFun s := ⟨fun x ↦ b.coord i (s x),
    (LinearMap.toContinuousLinearMap (b.coord i)).contMDiff.comp (trivialEquiv s).contMDiff⟩
  map_add' s t := ContMDiffMap.ext fun x ↦ (b.coord i).map_add (s x) (t x)
  map_smul' f s := ContMDiffMap.ext fun x ↦
    (congrArg (b.coord i) (ContMDiffSection.smul_apply f s x)).trans
      ((b.coord i).map_smul (f x) (s x))

@[simp] theorem trivialCoord_apply (b : Module.Basis ι 𝕜 F) (i : ι)
    (s : Cₛ^n⟮I; F, Bundle.Trivial M F⟯) (x : M) :
    trivialCoord b i s x = b.coord i (s x) := (rfl)

@[simp] theorem trivialCoord_trivialConst [DecidableEq ι] (b : Module.Basis ι 𝕜 F) (i j : ι) :
    trivialCoord b i (trivialConst I M n (b j)) = (if i = j then 1 else 0 : C^n⟮I, M; 𝕜⟯) := by
  ext x; by_cases h : i = j <;> simp [h, Module.Basis.coord_apply]

/-- Every `C^n` section of `Bundle.Trivial M F` expands in a finite basis of constant sections. -/
theorem eq_sum_trivialCoord_smul_trivialConst [Fintype ι] (b : Module.Basis ι 𝕜 F)
    (s : Cₛ^n⟮I; F, Bundle.Trivial M F⟯) :
    s = ∑ i, trivialCoord b i s • trivialConst I M n (b i) := by
  ext x
  have hsum := map_sum (evalLinearMap I F n (Bundle.Trivial M F) x)
    (fun i ↦ trivialCoord b i s • trivialConst I M n (b i)) Finset.univ
  rw [evalLinearMap_apply] at hsum
  exact (by simp [evalLinearMap_apply, Module.Basis.coord_apply] : s x = _).trans hsum.symm

end Basis

section TrivialModel

variable {𝕜 E H : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {W : Type*} [AddCommGroup W] [Module 𝕜 W] [TopologicalSpace W]
  [IsTopologicalAddGroup W] [ContinuousSMul 𝕜 W] [T2Space W] [FiniteDimensional 𝕜 W]
  {n : ℕ∞ω}

/-- The `C^n⟮I, M; 𝕜⟯`-linear equivalence between `C^n` sections of `Bundle.Trivial M W` (modelled
on `Bundle.TrivialModel 𝕜 W`) and `C^n` maps `M → Bundle.TrivialModel 𝕜 W`. -/
def modelEquiv :
    Cₛ^n⟮I; Bundle.TrivialModel 𝕜 W, Bundle.Trivial M W⟯ ≃ₗ[C^n⟮I, M; 𝕜⟯]
      C^n⟮I, M; 𝓘(𝕜, Bundle.TrivialModel 𝕜 W), Bundle.TrivialModel 𝕜 W⟯ where
  toFun s := ⟨fun x ↦ Bundle.TrivialModel.equiv 𝕜 W (s x),
    (Bundle.TrivialModel.contMDiff_mk_iff.1 s.contMDiff).2⟩
  invFun f := ⟨fun x ↦ (Bundle.TrivialModel.equiv 𝕜 W).symm (f x),
    Bundle.TrivialModel.contMDiff_mk_iff.2 ⟨contMDiff_id, by simpa using f.contMDiff⟩⟩
  left_inv _ := by ext x; simp
  right_inv _ := by ext x; simp
  map_add' s t := ContMDiffMap.ext fun x ↦ (Bundle.TrivialModel.equiv 𝕜 W).map_add (s x) (t x)
  map_smul' f s := ContMDiffMap.ext fun x ↦
    (congrArg (Bundle.TrivialModel.equiv 𝕜 W) (ContMDiffSection.smul_apply f s x)).trans
      ((Bundle.TrivialModel.equiv 𝕜 W).map_smul (f x) (s x))

@[simp] theorem modelEquiv_apply (s : Cₛ^n⟮I; Bundle.TrivialModel 𝕜 W, Bundle.Trivial M W⟯)
    (x : M) : modelEquiv s x = Bundle.TrivialModel.equiv 𝕜 W (s x) := (rfl)

@[simp] theorem modelEquiv_symm_apply
    (f : C^n⟮I, M; 𝓘(𝕜, Bundle.TrivialModel 𝕜 W), Bundle.TrivialModel 𝕜 W⟯) (x : M) :
    modelEquiv.symm f x = (Bundle.TrivialModel.equiv 𝕜 W).symm (f x) := (rfl)

variable (I M n) in
/-- Constant `C^n` sections of `Bundle.Trivial M W` (modelled on `Bundle.TrivialModel 𝕜 W`), as a
`𝕜`-linear map from `W`. -/
def modelConst : W →ₗ[𝕜] Cₛ^n⟮I; Bundle.TrivialModel 𝕜 W, Bundle.Trivial M W⟯ where
  toFun w := ⟨fun _ ↦ w, Bundle.TrivialModel.contMDiff_mk_iff.2 ⟨contMDiff_id, contMDiff_const⟩⟩
  map_add' _ _ := by ext x; rfl
  map_smul' _ _ := by ext x; rfl

@[simp] theorem modelConst_apply (w : W) (x : M) : modelConst I M n w x = w := (rfl)

theorem modelConst_injective [Nonempty M] :
    Function.Injective (modelConst I M n (W := W)) := fun _ _ h ↦ by
  obtain ⟨x₀⟩ := ‹Nonempty M›; simpa using congr($h x₀)

section PullbackMap

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  {W' : Type*} [AddCommGroup W'] [Module 𝕜 W'] [TopologicalSpace W'] [IsTopologicalAddGroup W']
  [ContinuousSMul 𝕜 W'] [T2Space W'] [FiniteDimensional 𝕜 W']

/-- Pullback of a `C^n` section of `Bundle.Trivial M W` along a `C^n` map `φ : N → M`. -/
def modelPullback (φ : C^n⟮J, N; I, M⟯)
    (s : Cₛ^n⟮I; Bundle.TrivialModel 𝕜 W, Bundle.Trivial M W⟯) :
    Cₛ^n⟮J; Bundle.TrivialModel 𝕜 W, Bundle.Trivial N W⟯ :=
  modelEquiv.symm ((modelEquiv s).comp φ)

@[simp] theorem modelPullback_apply (φ : C^n⟮J, N; I, M⟯)
    (s : Cₛ^n⟮I; Bundle.TrivialModel 𝕜 W, Bundle.Trivial M W⟯) (y : N) :
    modelPullback φ s y = s (φ y) := by simp [modelPullback]

/-- Pushforward of `C^n` sections of `Bundle.Trivial M W` along a `𝕜`-linear map `L : W →ₗ[𝕜] W'`,
as a `C^n⟮I, M; 𝕜⟯`-linear map. -/
def modelMap (L : W →ₗ[𝕜] W') :
    Cₛ^n⟮I; Bundle.TrivialModel 𝕜 W, Bundle.Trivial M W⟯ →ₗ[C^n⟮I, M; 𝕜⟯]
      Cₛ^n⟮I; Bundle.TrivialModel 𝕜 W', Bundle.Trivial M W'⟯ :=
  let L_mod : Bundle.TrivialModel 𝕜 W →L[𝕜] Bundle.TrivialModel 𝕜 W' :=
    LinearMap.toContinuousLinearMap ((Bundle.TrivialModel.equiv 𝕜 W').toLinearMap.comp
      (L.comp (Bundle.TrivialModel.equiv 𝕜 W).symm.toLinearMap))
  let hid := Bundle.TrivialModel.contMDiff_mk_iff.1 (contMDiff_id (I := I.prod _))
  have hL : ContMDiff (I.prod 𝓘(𝕜, Bundle.TrivialModel 𝕜 W))
      (I.prod 𝓘(𝕜, Bundle.TrivialModel 𝕜 W')) n
      (fun p : TotalSpace (Bundle.TrivialModel 𝕜 W) (Bundle.Trivial M W) ↦
        (⟨p.proj, L p.2⟩ : TotalSpace (Bundle.TrivialModel 𝕜 W') (Bundle.Trivial M W'))) :=
    Bundle.TrivialModel.contMDiff_mk_iff.2
      ⟨hid.1, (L_mod.contMDiff.comp hid.2).congr fun _ ↦ by simp [L_mod]⟩
  { (mapLinearMap (fun _ ↦ L) hL).toAddHom with
    map_smul' := mapLinearMap_smul_function (fun _ ↦ L) hL }

@[simp] theorem modelMap_apply (L : W →ₗ[𝕜] W')
    (s : Cₛ^n⟮I; Bundle.TrivialModel 𝕜 W, Bundle.Trivial M W⟯) (x : M) :
    modelMap L s x = L (s x) := by simp [modelMap]

end PullbackMap

/-- The `i`-th coordinate of a `C^n` section of `Bundle.Trivial M W` in a basis `b` of `W`. -/
def modelCoord {ι : Type*} (b : Module.Basis ι 𝕜 W) (i : ι) :
    Cₛ^n⟮I; Bundle.TrivialModel 𝕜 W, Bundle.Trivial M W⟯ →ₗ[C^n⟮I, M; 𝕜⟯] C^n⟮I, M; 𝕜⟯ where
  toFun s := ⟨fun x ↦ b.coord i (s x),
    (LinearMap.toContinuousLinearMap
      ((b.coord i).comp (Bundle.TrivialModel.equiv 𝕜 W).symm.toLinearMap)).contMDiff.comp
        (modelEquiv s).contMDiff |>.congr fun _ ↦ by simp⟩
  map_add' s t := ContMDiffMap.ext fun x ↦ (b.coord i).map_add (s x) (t x)
  map_smul' f s := ContMDiffMap.ext fun x ↦
    (congrArg (b.coord i) (ContMDiffSection.smul_apply f s x)).trans
      ((b.coord i).map_smul (f x) (s x))

@[simp] theorem modelCoord_apply {ι : Type*} (b : Module.Basis ι 𝕜 W) (i : ι)
    (s : Cₛ^n⟮I; Bundle.TrivialModel 𝕜 W, Bundle.Trivial M W⟯) (x : M) :
    modelCoord b i s x = b.coord i (s x) := (rfl)

/-- Every `C^n` section of `Bundle.Trivial M W` expands in a finite basis of constant sections. -/
theorem eq_sum_modelCoord_smul_modelConst {ι : Type*} [Fintype ι] (b : Module.Basis ι 𝕜 W)
    (s : Cₛ^n⟮I; Bundle.TrivialModel 𝕜 W, Bundle.Trivial M W⟯) :
    s = ∑ i, modelCoord b i s • modelConst I M n (b i) := by
  ext x
  have hsum := map_sum (evalLinearMap I (Bundle.TrivialModel 𝕜 W) n (Bundle.Trivial M W) x)
    (fun i ↦ modelCoord b i s • modelConst I M n (b i)) Finset.univ
  rw [evalLinearMap_apply] at hsum
  exact (by simp [evalLinearMap_apply, Module.Basis.coord_apply] : s x = _).trans hsum.symm

/-- Directional derivative of a smooth section `s` of `Bundle.Trivial M W` at `x : M`, independent
of any norm on `W`. -/
def modelDeriv (s : Cₛ^∞⟮I; Bundle.TrivialModel 𝕜 W, Bundle.Trivial M W⟯) (x : M) :
    TangentSpace I x →L[𝕜] W :=
  (Bundle.TrivialModel.equiv 𝕜 W).symm.toContinuousLinearMap ∘L mvfderiv I (modelEquiv s) x

theorem modelEquiv_modelDeriv_apply
    (s : Cₛ^∞⟮I; Bundle.TrivialModel 𝕜 W, Bundle.Trivial M W⟯) (x : M) (v : TangentSpace I x) :
    Bundle.TrivialModel.equiv 𝕜 W (modelDeriv s x v) = mvfderiv I (modelEquiv s) x v :=
  (Bundle.TrivialModel.equiv 𝕜 W).apply_symm_apply _

@[simp] theorem modelDeriv_zero (x : M) :
    modelDeriv (0 : Cₛ^∞⟮I; Bundle.TrivialModel 𝕜 W, Bundle.Trivial M W⟯) x = 0 := by
  ext v; simp [modelDeriv]

@[simp] theorem modelDeriv_modelConst (w : W) (x : M) :
    modelDeriv (modelConst I M ∞ w) x = 0 := by
  ext v; simp [modelDeriv, show ⇑(modelEquiv (modelConst I M ∞ w)) =
    fun _ : M ↦ Bundle.TrivialModel.equiv 𝕜 W w from rfl, mvfderiv_const]

theorem modelDeriv_add (s t : Cₛ^∞⟮I; Bundle.TrivialModel 𝕜 W, Bundle.Trivial M W⟯) (x : M) :
    modelDeriv (s + t) x = modelDeriv s x + modelDeriv t x := by
  ext v
  simp [modelDeriv, map_add, mvfderiv_add ((modelEquiv s).contMDiff.mdifferentiableAt (by simp))
    ((modelEquiv t).contMDiff.mdifferentiableAt (by simp))]

theorem modelDeriv_sub (s t : Cₛ^∞⟮I; Bundle.TrivialModel 𝕜 W, Bundle.Trivial M W⟯) (x : M) :
    modelDeriv (s - t) x = modelDeriv s x - modelDeriv t x := by
  ext v
  simp [modelDeriv, map_sub, mvfderiv_sub ((modelEquiv s).contMDiff.mdifferentiableAt (by simp))
    ((modelEquiv t).contMDiff.mdifferentiableAt (by simp))]

theorem modelDeriv_const_smul (c : 𝕜)
    (s : Cₛ^∞⟮I; Bundle.TrivialModel 𝕜 W, Bundle.Trivial M W⟯) (x : M) :
    modelDeriv (c • s) x = c • modelDeriv s x := by
  ext v; apply (Bundle.TrivialModel.equiv 𝕜 W).injective
  have hcs : ⇑(modelEquiv (c • s)) = (fun _ : M ↦ c) • ⇑(modelEquiv s) :=
    funext fun y ↦ (Bundle.TrivialModel.equiv 𝕜 W).map_smul c (s y)
  rw [_root_.smul_apply, map_smul, modelEquiv_modelDeriv_apply, modelEquiv_modelDeriv_apply, hcs,
    mvfderiv_smul mdifferentiableAt_const ((modelEquiv s).contMDiff.mdifferentiableAt (by simp))]
  simp [mvfderiv_const]

/-- The Leibniz rule for `modelDeriv` on scalar-function multiples of sections. -/
theorem modelDeriv_smul (f : C^∞⟮I, M; 𝕜⟯)
    (s : Cₛ^∞⟮I; Bundle.TrivialModel 𝕜 W, Bundle.Trivial M W⟯) (x : M) (v : TangentSpace I x) :
    modelDeriv (f • s) x v = f x • modelDeriv s x v + mvfderiv I f x v • s x := by
  apply (Bundle.TrivialModel.equiv 𝕜 W).injective
  have hfs : ⇑(modelEquiv (f • s)) = (⇑f : M → 𝕜) • (⇑(modelEquiv s) : M → _) :=
    funext fun y ↦ (modelEquiv_apply (f • s) y).trans <| by
      rw [ContMDiffSection.smul_apply, map_smul]; rfl
  rw [map_add, map_smul, map_smul, modelEquiv_modelDeriv_apply, modelEquiv_modelDeriv_apply,
    ← modelEquiv_apply, hfs, mvfderiv_smul (f.contMDiff.mdifferentiableAt (by simp))
      ((modelEquiv s).contMDiff.mdifferentiableAt (by simp))]; rfl

/-- Directional derivative of a smooth section `s` of `Bundle.Trivial M W` along a smooth vector
field `X`, packaged as a smooth section of `Bundle.Trivial M W`. -/
def modelLieDeriv [IsManifold I ∞ M] (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (s : Cₛ^∞⟮I; Bundle.TrivialModel 𝕜 W, Bundle.Trivial M W⟯) :
    Cₛ^∞⟮I; Bundle.TrivialModel 𝕜 W, Bundle.Trivial M W⟯ :=
  modelEquiv.symm ⟨fun x ↦ mvfderiv I (modelEquiv s) x (X x),
    contMDiffOn_univ.1 <| (modelEquiv s).contMDiff.contMDiffOn.contMDiffOn_mvfderiv_apply
      isOpen_univ X.contMDiff.contMDiffOn (by simp)⟩

@[simp] theorem modelLieDeriv_apply [IsManifold I ∞ M]
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (s : Cₛ^∞⟮I; Bundle.TrivialModel 𝕜 W, Bundle.Trivial M W⟯) (x : M) :
    modelLieDeriv X s x = modelDeriv s x (X x) := (rfl)

theorem modelEquiv_modelLieDeriv_apply [IsManifold I ∞ M]
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (s : Cₛ^∞⟮I; Bundle.TrivialModel 𝕜 W, Bundle.Trivial M W⟯) (x : M) :
    modelEquiv (modelLieDeriv X s) x = mvfderiv I (modelEquiv s) x (X x) :=
  DFunLike.congr_fun (modelEquiv.apply_symm_apply _) x

/-- `modelDeriv` sends the manifold Lie bracket of two smooth vector fields to the commutator of
their directional derivatives on smooth sections of `Bundle.Trivial M W`. -/
theorem modelDeriv_mlieBracket [IsRCLikeNormedField 𝕜] [CompleteSpace E] [IsManifold I ∞ M]
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (s : Cₛ^∞⟮I; Bundle.TrivialModel 𝕜 W, Bundle.Trivial M W⟯) (x : M) :
    modelDeriv s x (mlieBracket I X Y x) =
      modelDeriv (modelLieDeriv Y s) x (X x) - modelDeriv (modelLieDeriv X s) x (Y x) := by
  have : IsManifold I (minSmoothness 𝕜 2) M := IsManifold.of_le (n := ∞) (by simp)
  apply (Bundle.TrivialModel.equiv 𝕜 W).injective
  rw [map_sub, modelEquiv_modelDeriv_apply, modelEquiv_modelDeriv_apply,
    modelEquiv_modelDeriv_apply, funext (modelEquiv_modelLieDeriv_apply Y s),
    funext (modelEquiv_modelLieDeriv_apply X s)]
  exact mvfderiv_mlieBracket (modelEquiv s).contMDiff.contMDiffAt (by simp)
    (X.contMDiff.mdifferentiableAt (by simp)) (Y.contMDiff.mdifferentiableAt (by simp))

/-- Chain rule for `modelDeriv` along a smooth map `φ : N → M`. -/
theorem modelDeriv_modelPullback {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'} [TopologicalSpace N] [ChartedSpace H' N]
    (φ : C^∞⟮J, N; I, M⟯) (s : Cₛ^∞⟮I; Bundle.TrivialModel 𝕜 W, Bundle.Trivial M W⟯) (y : N)
    (v : TangentSpace J y) :
    modelDeriv (modelPullback φ s) y v = modelDeriv s (φ y) (mfderiv J I φ y v) := by
  apply (Bundle.TrivialModel.equiv 𝕜 W).injective
  have hcomp : ⇑(modelEquiv (modelPullback φ s)) = ⇑(modelEquiv s) ∘ ⇑φ := funext fun _ ↦ by simp
  rw [modelEquiv_modelDeriv_apply, modelEquiv_modelDeriv_apply, hcomp]
  exact mvfderiv_comp_apply y ((modelEquiv s).contMDiff.mdifferentiableAt (by simp))
    (φ.contMDiff.mdifferentiableAt (by simp)) v

/-- Fibrewise linear pushforward along `L : W →ₗ[𝕜] W'` commutes with `modelDeriv`. -/
theorem modelDeriv_modelMap {W' : Type*} [AddCommGroup W'] [Module 𝕜 W']
    [TopologicalSpace W'] [IsTopologicalAddGroup W'] [ContinuousSMul 𝕜 W'] [T2Space W']
    [FiniteDimensional 𝕜 W'] (L : W →ₗ[𝕜] W')
    (s : Cₛ^∞⟮I; Bundle.TrivialModel 𝕜 W, Bundle.Trivial M W⟯) (x : M) (v : TangentSpace I x) :
    modelDeriv (modelMap L s) x v = L (modelDeriv s x v) := by
  let L_mod : Bundle.TrivialModel 𝕜 W →L[𝕜] Bundle.TrivialModel 𝕜 W' :=
    LinearMap.toContinuousLinearMap ((Bundle.TrivialModel.equiv 𝕜 W').toLinearMap.comp
      (L.comp (Bundle.TrivialModel.equiv 𝕜 W).symm.toLinearMap))
  apply (Bundle.TrivialModel.equiv 𝕜 W').injective
  have hcomp : ⇑(modelEquiv (modelMap L s)) = ⇑L_mod ∘ ⇑(modelEquiv s) := by
    funext y; simp [L_mod]
  rw [modelEquiv_modelDeriv_apply, hcomp, mvfderiv_comp_apply x L_mod.mdifferentiableAt
    ((modelEquiv s).contMDiff.mdifferentiableAt (by simp)) v, mvfderiv_eq_fderiv, L_mod.fderiv]
  exact (congrArg L_mod (modelEquiv_modelDeriv_apply s x v)).symm.trans (by simp [L_mod])

/-- When the fibre `F` is a normed space, `modelDeriv` agrees with `mvfderiv`. -/
theorem modelDeriv_eq_mvfderiv {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [FiniteDimensional 𝕜 F] (s : Cₛ^∞⟮I; Bundle.TrivialModel 𝕜 F, Bundle.Trivial M F⟯) (x : M) :
    modelDeriv s x = mvfderiv I s x := by
  let e := Bundle.TrivialModel.equiv 𝕜 F
  have hs : ⇑s = ⇑e.symm.toContinuousLinearMap ∘ ⇑(modelEquiv s) :=
    funext fun y ↦ (e.symm_apply_apply (s y)).symm
  ext v; conv_rhs => rw [hs]
  rw [mvfderiv_comp_apply x e.symm.toContinuousLinearMap.mdifferentiableAt
    ((modelEquiv s).contMDiff.mdifferentiableAt (by simp)) v, mvfderiv_eq_fderiv,
    ContinuousLinearMap.fderiv]; rfl

end TrivialModel

end ContMDiffSection
