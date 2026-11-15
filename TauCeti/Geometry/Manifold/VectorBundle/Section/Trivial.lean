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
(`ContMDiffSection.trivialEquiv`). For a finite-dimensional Hausdorff topological module `W`,
`TauCeti.TrivialModel 𝕜 W` equips `Bundle.Trivial M W` with `modelEquiv`, `modelConst`,
`modelCoord`, `modelMap`, `modelPullback`, `modelDeriv`, and `modelLieDeriv`.
-/
public section
noncomputable section

open Bundle Manifold Set TauCeti VectorField
open scoped Manifold ContDiff

namespace ContMDiffSection

variable {𝕜 E H : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ∞ω}

/-- The `C^n⟮I, M; 𝕜⟯`-linear equivalence between `C^n` sections of `Bundle.Trivial M F` and `C^n`
maps `M → F`. -/
def trivialEquiv : Cₛ^n⟮I; F, Bundle.Trivial M F⟯ ≃ₗ[C^n⟮I, M; 𝕜⟯] C^n⟮I, M; 𝓘(𝕜, F), F⟯ :=
  ⟨⟨⟨fun s ↦ ⟨fun x ↦ s x, (Bundle.Trivial.contMDiff_mk_iff.1 s.contMDiff).2⟩,
    fun _ _ ↦ by ext x; rfl⟩,
    fun f s ↦ ContMDiffMap.ext fun x ↦ ContMDiffSection.smul_apply f s x⟩,
    fun f ↦ ⟨fun x ↦ f x, Bundle.Trivial.contMDiff_mk_iff.2 ⟨contMDiff_id, f.contMDiff⟩⟩,
    fun _ ↦ by ext x; rfl, fun _ ↦ by ext x; rfl⟩

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
def trivialConst : F →ₗ[𝕜] Cₛ^n⟮I; F, Bundle.Trivial M F⟯ :=
  ⟨⟨fun v ↦ trivialEquiv.symm (ContMDiffMap.const v), fun _ _ ↦ by ext x; rfl⟩,
    fun _ _ ↦ by ext x; rfl⟩

@[simp] theorem trivialConst_apply (v : F) (x : M) : trivialConst I M n v x = v := (rfl)

@[simp] theorem coe_trivialConst (v : F) : ⇑(trivialConst I M n v) = Function.const M v := (rfl)

@[simp] theorem trivialEquiv_trivialConst (v : F) :
    trivialEquiv (trivialConst I M n v) = ContMDiffMap.const v := (rfl)

theorem trivialConst_injective [Nonempty M] :
    Function.Injective (trivialConst I M n (F := F)) := fun _ _ h ↦ by
  obtain ⟨x₀⟩ := ‹Nonempty M›; simpa using congr($h x₀)

section Basis

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] {ι : Type*} (b : Module.Basis ι 𝕜 F)

/-- The `i`-th coordinate of a `C^n` section of `Bundle.Trivial M F` in a basis `b` of `F`. -/
def trivialCoord (i : ι) : Cₛ^n⟮I; F, Bundle.Trivial M F⟯ →ₗ[C^n⟮I, M; 𝕜⟯] C^n⟮I, M; 𝕜⟯ :=
  ⟨⟨fun s ↦ ⟨fun x ↦ b.coord i (s x),
      (LinearMap.toContinuousLinearMap (b.coord i)).contMDiff.comp (trivialEquiv s).contMDiff⟩,
    fun s t ↦ ContMDiffMap.ext fun x ↦ (b.coord i).map_add (s x) (t x)⟩,
    fun f s ↦ ContMDiffMap.ext fun x ↦ (congrArg (b.coord i)
      (ContMDiffSection.smul_apply f s x)).trans ((b.coord i).map_smul (f x) (s x))⟩

@[simp] theorem trivialCoord_apply (i : ι) (s : Cₛ^n⟮I; F, Bundle.Trivial M F⟯) (x : M) :
    trivialCoord b i s x = b.coord i (s x) := (rfl)

@[simp] theorem trivialCoord_trivialConst [DecidableEq ι] (i j : ι) :
    trivialCoord b i (trivialConst I M n (b j)) = (if i = j then 1 else 0 : C^n⟮I, M; 𝕜⟯) := by
  ext x; by_cases h : i = j <;> simp [h, Module.Basis.coord_apply]

/-- Every `C^n` section of `Bundle.Trivial M F` expands in a finite basis of constant sections. -/
theorem eq_sum_trivialCoord_smul_trivialConst [Fintype ι] (s : Cₛ^n⟮I; F, Bundle.Trivial M F⟯) :
    s = ∑ i, trivialCoord b i s • trivialConst I M n (b i) := by
  ext x; have hsum := map_sum (evalLinearMap I F n (Bundle.Trivial M F) x)
    (fun i ↦ trivialCoord b i s • trivialConst I M n (b i)) Finset.univ
  rw [evalLinearMap_apply] at hsum
  exact (by simp [evalLinearMap_apply, Module.Basis.coord_apply] : s x = _).trans hsum.symm

end Basis

section TrivialModel

variable {𝕜 E H : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] {W : Type*} [AddCommGroup W] [Module 𝕜 W]
  [TopologicalSpace W] [IsTopologicalAddGroup W] [ContinuousSMul 𝕜 W] [T2Space W]
  [FiniteDimensional 𝕜 W] {n : ℕ∞ω}

/-- The `C^n⟮I, M; 𝕜⟯`-linear equivalence between `C^n` sections of `Bundle.Trivial M W` and `C^n`
maps `M → TauCeti.TrivialModel 𝕜 W`. -/
def modelEquiv : Cₛ^n⟮I; TrivialModel 𝕜 W, Bundle.Trivial M W⟯ ≃ₗ[C^n⟮I, M; 𝕜⟯]
    C^n⟮I, M; 𝓘(𝕜, TrivialModel 𝕜 W), TrivialModel 𝕜 W⟯ :=
  ⟨⟨⟨fun s ↦ ⟨fun x ↦ TrivialModel.equiv 𝕜 W (s x),
      (TrivialModel.contMDiff_mk_iff.1 s.contMDiff).2⟩,
    fun s t ↦ ContMDiffMap.ext fun x ↦ (TrivialModel.equiv 𝕜 W).map_add (s x) (t x)⟩,
    fun f s ↦ ContMDiffMap.ext fun x ↦ (congrArg (TrivialModel.equiv 𝕜 W)
      (ContMDiffSection.smul_apply f s x)).trans ((TrivialModel.equiv 𝕜 W).map_smul (f x) (s x))⟩,
    fun f ↦ ⟨fun x ↦ (TrivialModel.equiv 𝕜 W).symm (f x),
      TrivialModel.contMDiff_mk_iff.2 ⟨contMDiff_id, by simpa using f.contMDiff⟩⟩,
    fun _ ↦ by ext x; simp, fun _ ↦ by ext x; simp⟩

@[simp] theorem modelEquiv_apply (s : Cₛ^n⟮I; TrivialModel 𝕜 W, Bundle.Trivial M W⟯) (x : M) :
    modelEquiv s x = TrivialModel.equiv 𝕜 W (s x) := (rfl)

@[simp] theorem modelEquiv_symm_apply
    (f : C^n⟮I, M; 𝓘(𝕜, TrivialModel 𝕜 W), TrivialModel 𝕜 W⟯) (x : M) :
    modelEquiv.symm f x = (TrivialModel.equiv 𝕜 W).symm (f x) := (rfl)

variable (I M n) in
/-- Constant `C^n` sections of `Bundle.Trivial M W`, as a `𝕜`-linear map from `W`. -/
def modelConst : W →ₗ[𝕜] Cₛ^n⟮I; TrivialModel 𝕜 W, Bundle.Trivial M W⟯ :=
  ⟨⟨fun w ↦ ⟨fun _ ↦ w, TrivialModel.contMDiff_mk_iff.2 ⟨contMDiff_id, contMDiff_const⟩⟩,
    fun _ _ ↦ by ext x; rfl⟩, fun _ _ ↦ by ext x; rfl⟩

@[simp] theorem modelConst_apply (w : W) (x : M) : modelConst I M n w x = w := (rfl)

@[simp] theorem coe_modelConst (w : W) : ⇑(modelConst I M n w) = Function.const M w := (rfl)

@[simp] theorem modelEquiv_modelConst (w : W) :
    modelEquiv (modelConst I M n w) = ContMDiffMap.const (TrivialModel.equiv 𝕜 W w) := (rfl)

theorem modelConst_injective [Nonempty M] :
    Function.Injective (modelConst I M n (W := W)) := fun _ _ h ↦ by
  obtain ⟨x₀⟩ := ‹Nonempty M›; simpa using congr($h x₀)

section PullbackMap

variable {E' H' N E'' H'' P W' W'' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [TopologicalSpace H'']
  {K : ModelWithCorners 𝕜 E'' H''} [TopologicalSpace P] [ChartedSpace H'' P]
  [AddCommGroup W'] [Module 𝕜 W'] [TopologicalSpace W'] [IsTopologicalAddGroup W']
  [ContinuousSMul 𝕜 W'] [T2Space W'] [FiniteDimensional 𝕜 W']
  [AddCommGroup W''] [Module 𝕜 W''] [TopologicalSpace W''] [IsTopologicalAddGroup W'']
  [ContinuousSMul 𝕜 W''] [T2Space W''] [FiniteDimensional 𝕜 W'']

/-- Pullback of `C^n` sections of `Bundle.Trivial M W` along a `C^n` map `φ : N → M`. -/
def modelPullback (φ : C^n⟮J, N; I, M⟯) :
    Cₛ^n⟮I; TrivialModel 𝕜 W, Bundle.Trivial M W⟯ →ₗ[𝕜]
      Cₛ^n⟮J; TrivialModel 𝕜 W, Bundle.Trivial N W⟯ :=
  ⟨⟨fun s ↦ modelEquiv.symm ((modelEquiv s).comp φ), fun _ _ ↦ by ext y; simp⟩,
    fun _ _ ↦ by ext y; simp⟩

@[simp] theorem modelPullback_apply (φ : C^n⟮J, N; I, M⟯)
    (s : Cₛ^n⟮I; TrivialModel 𝕜 W, Bundle.Trivial M W⟯) (y : N) :
    modelPullback φ s y = s (φ y) := by simp [modelPullback]

@[simp] theorem modelPullback_smul_function (φ : C^n⟮J, N; I, M⟯) (f : C^n⟮I, M; 𝕜⟯)
    (s : Cₛ^n⟮I; TrivialModel 𝕜 W, Bundle.Trivial M W⟯) :
    modelPullback φ (f • s) = f.comp φ • modelPullback φ s := by ext y; simp

@[simp] theorem modelPullback_modelConst (φ : C^n⟮J, N; I, M⟯) (w : W) :
    modelPullback φ (modelConst I M n w) = modelConst J N n w := by ext y; simp

@[simp] theorem modelPullback_id :
    modelPullback (ContMDiffMap.id : C^n⟮I, M; I, M⟯) =
      LinearMap.id (R := 𝕜) (M := Cₛ^n⟮I; TrivialModel 𝕜 W, Bundle.Trivial M W⟯) := by
  ext s x; rw [modelPullback_apply]; rfl

theorem modelPullback_comp (φ : C^n⟮J, N; I, M⟯) (ψ : C^n⟮K, P; J, N⟯) :
    modelPullback (W := W) (φ.comp ψ) = (modelPullback ψ).comp (modelPullback φ) := by ext s z; simp

/-- Pushforward of `C^n` sections of `Bundle.Trivial M W` along `L : W →ₗ[𝕜] W'`. -/
def modelMap (L : W →ₗ[𝕜] W') :
    Cₛ^n⟮I; TrivialModel 𝕜 W, Bundle.Trivial M W⟯ →ₗ[C^n⟮I, M; 𝕜⟯]
      Cₛ^n⟮I; TrivialModel 𝕜 W', Bundle.Trivial M W'⟯ :=
  let L_mod : TrivialModel 𝕜 W →L[𝕜] TrivialModel 𝕜 W' := LinearMap.toContinuousLinearMap
    ((TrivialModel.equiv 𝕜 W').toLinearMap.comp (L.comp (TrivialModel.equiv 𝕜 W).symm.toLinearMap))
  let hid := TrivialModel.contMDiff_mk_iff.1 (contMDiff_id (I := I.prod _))
  have hL : ContMDiff (I.prod 𝓘(𝕜, TrivialModel 𝕜 W)) (I.prod 𝓘(𝕜, TrivialModel 𝕜 W')) n
      (fun p : TotalSpace (TrivialModel 𝕜 W) (Bundle.Trivial M W) ↦
        (⟨p.proj, L p.2⟩ : TotalSpace (TrivialModel 𝕜 W') (Bundle.Trivial M W'))) :=
    TrivialModel.contMDiff_mk_iff.2
      ⟨hid.1, (L_mod.contMDiff.comp hid.2).congr fun _ ↦ by simp [L_mod]⟩
  ⟨(mapLinearMap (fun _ ↦ L) hL).toAddHom, mapLinearMap_smul_function (fun _ ↦ L) hL⟩

@[simp] theorem modelMap_apply (L : W →ₗ[𝕜] W')
    (s : Cₛ^n⟮I; TrivialModel 𝕜 W, Bundle.Trivial M W⟯) (x : M) :
    modelMap L s x = L (s x) := by simp [modelMap]

@[simp] theorem modelMap_modelConst (L : W →ₗ[𝕜] W') (w : W) :
    modelMap L (modelConst I M n w) = modelConst I M n (L w) := by ext x; simp

@[simp] theorem modelMap_id : modelMap (LinearMap.id : W →ₗ[𝕜] W) =
    LinearMap.id (R := C^n⟮I, M; 𝕜⟯) (M := Cₛ^n⟮I; TrivialModel 𝕜 W, Bundle.Trivial M W⟯) := by
  ext s x; simp

theorem modelMap_comp (L₂ : W' →ₗ[𝕜] W'') (L₁ : W →ₗ[𝕜] W') :
    modelMap (I := I) (M := M) (n := n) (L₂.comp L₁) = (modelMap L₂).comp (modelMap L₁) := by
  ext s x; simp

end PullbackMap

/-- The `i`-th coordinate of a `C^n` section of `Bundle.Trivial M W` in a basis `b` of `W`. -/
def modelCoord {ι : Type*} (b : Module.Basis ι 𝕜 W) (i : ι) :
    Cₛ^n⟮I; TrivialModel 𝕜 W, Bundle.Trivial M W⟯ →ₗ[C^n⟮I, M; 𝕜⟯] C^n⟮I, M; 𝕜⟯ :=
  ⟨⟨fun s ↦ ⟨fun x ↦ b.coord i (s x), (LinearMap.toContinuousLinearMap
      ((b.coord i).comp (TrivialModel.equiv 𝕜 W).symm.toLinearMap)).contMDiff.comp
        (modelEquiv s).contMDiff |>.congr fun _ ↦ by simp⟩,
    fun s t ↦ ContMDiffMap.ext fun x ↦ (b.coord i).map_add (s x) (t x)⟩,
    fun f s ↦ ContMDiffMap.ext fun x ↦ (congrArg (b.coord i)
      (ContMDiffSection.smul_apply f s x)).trans ((b.coord i).map_smul (f x) (s x))⟩

@[simp] theorem modelCoord_apply {ι : Type*} (b : Module.Basis ι 𝕜 W) (i : ι)
    (s : Cₛ^n⟮I; TrivialModel 𝕜 W, Bundle.Trivial M W⟯) (x : M) :
    modelCoord b i s x = b.coord i (s x) := (rfl)

@[simp] theorem modelCoord_modelConst {ι : Type*} [DecidableEq ι] (b : Module.Basis ι 𝕜 W)
    (i j : ι) :
    modelCoord b i (modelConst I M n (b j)) = (if i = j then 1 else 0 : C^n⟮I, M; 𝕜⟯) := by
  ext x; by_cases h : i = j <;> simp [h, Module.Basis.coord_apply]

/-- Every `C^n` section of `Bundle.Trivial M W` expands in a finite basis of constant sections. -/
theorem eq_sum_modelCoord_smul_modelConst {ι : Type*} [Fintype ι] (b : Module.Basis ι 𝕜 W)
    (s : Cₛ^n⟮I; TrivialModel 𝕜 W, Bundle.Trivial M W⟯) :
    s = ∑ i, modelCoord b i s • modelConst I M n (b i) := by
  ext x; have hsum := map_sum (evalLinearMap I (TrivialModel 𝕜 W) n (Bundle.Trivial M W) x)
    (fun i ↦ modelCoord b i s • modelConst I M n (b i)) Finset.univ
  rw [evalLinearMap_apply] at hsum
  exact (by simp [evalLinearMap_apply, Module.Basis.coord_apply] : s x = _).trans hsum.symm

/-- Norm-independent directional derivative of a `C^n` section `s` of `Bundle.Trivial M W`. -/
def modelDeriv (s : Cₛ^n⟮I; TrivialModel 𝕜 W, Bundle.Trivial M W⟯) (x : M) :
    TangentSpace I x →L[𝕜] W :=
  (TrivialModel.equiv 𝕜 W).symm.toContinuousLinearMap ∘L mvfderiv I (modelEquiv s) x

theorem modelEquiv_modelDeriv_apply (s : Cₛ^n⟮I; TrivialModel 𝕜 W, Bundle.Trivial M W⟯) (x : M)
    (v : TangentSpace I x) :
    TrivialModel.equiv 𝕜 W (modelDeriv s x v) = mvfderiv I (modelEquiv s) x v :=
  (TrivialModel.equiv 𝕜 W).apply_symm_apply _

@[simp] theorem modelDeriv_zero (x : M) :
    modelDeriv (0 : Cₛ^n⟮I; TrivialModel 𝕜 W, Bundle.Trivial M W⟯) x = 0 := by
  ext v; simp [modelDeriv]

@[simp] theorem modelDeriv_modelConst (w : W) (x : M) :
    modelDeriv (modelConst I M n w) x = 0 := by
  ext v; rw [modelDeriv, modelEquiv_modelConst]; simp [ContMDiffMap.const, mvfderiv_const]

@[simp] theorem modelDeriv_neg (s : Cₛ^n⟮I; TrivialModel 𝕜 W, Bundle.Trivial M W⟯) (x : M) :
    modelDeriv (-s) x = -modelDeriv s x := by
  ext v; simp [modelDeriv, map_neg, ContMDiffMap.coe_neg, mvfderiv_neg]

@[simp] theorem modelDeriv_add (s t : Cₛ^n⟮I; TrivialModel 𝕜 W, Bundle.Trivial M W⟯) (x : M)
    (hn : n ≠ 0 := by simp) : modelDeriv (s + t) x = modelDeriv s x + modelDeriv t x := by
  ext v; simp [modelDeriv, map_add, mvfderiv_add ((modelEquiv s).contMDiff.mdifferentiableAt hn)
    ((modelEquiv t).contMDiff.mdifferentiableAt hn)]

@[simp] theorem modelDeriv_sub (s t : Cₛ^n⟮I; TrivialModel 𝕜 W, Bundle.Trivial M W⟯) (x : M)
    (hn : n ≠ 0 := by simp) : modelDeriv (s - t) x = modelDeriv s x - modelDeriv t x := by
  ext v; simp [modelDeriv, map_sub, mvfderiv_sub ((modelEquiv s).contMDiff.mdifferentiableAt hn)
    ((modelEquiv t).contMDiff.mdifferentiableAt hn)]

@[simp] theorem modelDeriv_const_smul (c : 𝕜)
    (s : Cₛ^n⟮I; TrivialModel 𝕜 W, Bundle.Trivial M W⟯) (x : M) :
    modelDeriv (c • s) x = c • modelDeriv s x := by
  ext v; apply (TrivialModel.equiv 𝕜 W).injective
  have hcs : ⇑(modelEquiv (c • s)) = c • ⇑(modelEquiv s) :=
    funext fun y ↦ (TrivialModel.equiv 𝕜 W).map_smul c (s y)
  rw [_root_.smul_apply, map_smul, modelEquiv_modelDeriv_apply, modelEquiv_modelDeriv_apply, hcs,
    TauCeti.mvfderiv_const_smul_field, _root_.smul_apply]

@[simp] theorem modelDeriv_smul (f : C^n⟮I, M; 𝕜⟯)
    (s : Cₛ^n⟮I; TrivialModel 𝕜 W, Bundle.Trivial M W⟯) (x : M) (v : TangentSpace I x)
    (hn : n ≠ 0 := by simp) :
    modelDeriv (f • s) x v = f x • modelDeriv s x v + mvfderiv I f x v • s x := by
  apply (TrivialModel.equiv 𝕜 W).injective
  have hfs : ⇑(modelEquiv (f • s)) = (⇑f : M → 𝕜) • (⇑(modelEquiv s) : M → _) :=
    funext fun y ↦ (modelEquiv_apply (f • s) y).trans <| by
      rw [ContMDiffSection.smul_apply, map_smul]; rfl
  rw [map_add, map_smul, map_smul, modelEquiv_modelDeriv_apply, modelEquiv_modelDeriv_apply,
    ← modelEquiv_apply, hfs, mvfderiv_smul (f.contMDiff.mdifferentiableAt hn)
      ((modelEquiv s).contMDiff.mdifferentiableAt hn)]; rfl

/-- Directional derivative of a `C^n` section `s` along a `C^m` vector field `X` (`m + 1 ≤ n`). -/
def modelLieDeriv [IsManifold I 1 M] {m : ℕ∞ω} (X : Cₛ^m⟮I; E, (TangentSpace I : M → Type _)⟯)
    (s : Cₛ^n⟮I; TrivialModel 𝕜 W, Bundle.Trivial M W⟯) (hmn : m + 1 ≤ n := by simp) :
    Cₛ^m⟮I; TrivialModel 𝕜 W, Bundle.Trivial M W⟯ :=
  modelEquiv.symm ⟨fun x ↦ mvfderiv I (modelEquiv s) x (X x),
    contMDiffOn_univ.1 <| (modelEquiv s).contMDiff.contMDiffOn.contMDiffOn_mvfderiv_apply
      isOpen_univ X.contMDiff.contMDiffOn hmn⟩

@[simp] theorem modelLieDeriv_apply [IsManifold I 1 M] {m : ℕ∞ω}
    (X : Cₛ^m⟮I; E, (TangentSpace I : M → Type _)⟯)
    (s : Cₛ^n⟮I; TrivialModel 𝕜 W, Bundle.Trivial M W⟯) (hmn : m + 1 ≤ n) (x : M) :
    modelLieDeriv X s hmn x = modelDeriv s x (X x) := (rfl)

theorem modelEquiv_modelLieDeriv_apply [IsManifold I 1 M] {m : ℕ∞ω}
    (X : Cₛ^m⟮I; E, (TangentSpace I : M → Type _)⟯)
    (s : Cₛ^n⟮I; TrivialModel 𝕜 W, Bundle.Trivial M W⟯) (hmn : m + 1 ≤ n) (x : M) :
    modelEquiv (modelLieDeriv X s hmn) x = mvfderiv I (modelEquiv s) x (X x) :=
  DFunLike.congr_fun (modelEquiv.apply_symm_apply _) x

/-- `modelDeriv` sends the manifold Lie bracket of two `C^m` vector fields to the commutator of
their directional derivatives on `C^n` sections. -/
theorem modelDeriv_mlieBracket [CompleteSpace E] [IsManifold I 1 M]
    [IsManifold I (minSmoothness 𝕜 2) M] {m : ℕ∞ω}
    (X Y : Cₛ^m⟮I; E, (TangentSpace I : M → Type _)⟯)
    (s : Cₛ^n⟮I; TrivialModel 𝕜 W, Bundle.Trivial M W⟯) (x : M)
    (hm : m ≠ 0 := by simp) (hmn : m + 1 ≤ n := by simp) (hn : minSmoothness 𝕜 2 ≤ n := by simp) :
    modelDeriv s x (mlieBracket I X Y x) =
      modelDeriv (modelLieDeriv Y s hmn) x (X x) - modelDeriv (modelLieDeriv X s hmn) x (Y x) := by
  apply (TrivialModel.equiv 𝕜 W).injective
  rw [map_sub, modelEquiv_modelDeriv_apply, modelEquiv_modelDeriv_apply,
    modelEquiv_modelDeriv_apply, funext (modelEquiv_modelLieDeriv_apply Y s hmn),
    funext (modelEquiv_modelLieDeriv_apply X s hmn)]
  exact mvfderiv_mlieBracket (modelEquiv s).contMDiff.contMDiffAt hn
    (X.contMDiff.mdifferentiableAt hm) (Y.contMDiff.mdifferentiableAt hm)

@[simp] theorem modelDeriv_modelPullback {E' H' N : Type*} [NormedAddCommGroup E']
    [NormedSpace 𝕜 E'] [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'} [TopologicalSpace N]
    [ChartedSpace H' N] (φ : C^n⟮J, N; I, M⟯)
    (s : Cₛ^n⟮I; TrivialModel 𝕜 W, Bundle.Trivial M W⟯) (y : N) (v : TangentSpace J y)
    (hn : n ≠ 0 := by simp) :
    modelDeriv (modelPullback φ s) y v = modelDeriv s (φ y) (mfderiv J I φ y v) := by
  apply (TrivialModel.equiv 𝕜 W).injective
  have hcomp : ⇑(modelEquiv (modelPullback φ s)) = ⇑(modelEquiv s) ∘ ⇑φ := funext fun _ ↦ by simp
  rw [modelEquiv_modelDeriv_apply, modelEquiv_modelDeriv_apply, hcomp]
  exact mvfderiv_comp_apply y ((modelEquiv s).contMDiff.mdifferentiableAt hn)
    (φ.contMDiff.mdifferentiableAt hn) v

@[simp] theorem modelDeriv_modelMap {W' : Type*} [AddCommGroup W'] [Module 𝕜 W']
    [TopologicalSpace W'] [IsTopologicalAddGroup W'] [ContinuousSMul 𝕜 W'] [T2Space W']
    [FiniteDimensional 𝕜 W'] (L : W →ₗ[𝕜] W')
    (s : Cₛ^n⟮I; TrivialModel 𝕜 W, Bundle.Trivial M W⟯) (x : M) (v : TangentSpace I x)
    (hn : n ≠ 0 := by simp) : modelDeriv (modelMap L s) x v = L (modelDeriv s x v) := by
  let L_mod : TrivialModel 𝕜 W →L[𝕜] TrivialModel 𝕜 W' := LinearMap.toContinuousLinearMap
    ((TrivialModel.equiv 𝕜 W').toLinearMap.comp (L.comp (TrivialModel.equiv 𝕜 W).symm.toLinearMap))
  apply (TrivialModel.equiv 𝕜 W').injective
  have hcomp : ⇑(modelEquiv (modelMap L s)) = ⇑L_mod ∘ ⇑(modelEquiv s) := funext fun _ ↦ by
    simp [L_mod]
  rw [modelEquiv_modelDeriv_apply, hcomp,
    L_mod.mvfderiv_comp_apply ((modelEquiv s).contMDiff.mdifferentiableAt hn) v]
  exact (congrArg L_mod (modelEquiv_modelDeriv_apply s x v)).symm.trans (by simp [L_mod])

theorem modelDeriv_eq_mvfderiv {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [FiniteDimensional 𝕜 F] (s : Cₛ^n⟮I; TrivialModel 𝕜 F, Bundle.Trivial M F⟯) (x : M)
    (hn : n ≠ 0 := by simp) : modelDeriv s x = mvfderiv I s x := by
  let e := TrivialModel.equiv 𝕜 F
  have hs : ⇑s = ⇑e.symm.toContinuousLinearMap ∘ ⇑(modelEquiv s) :=
    funext fun y ↦ (e.symm_apply_apply (s y)).symm
  ext v; conv_rhs => rw [hs]
  exact (e.symm.toContinuousLinearMap.mvfderiv_comp_apply
    ((modelEquiv s).contMDiff.mdifferentiableAt hn) v).symm

end TrivialModel
end ContMDiffSection
