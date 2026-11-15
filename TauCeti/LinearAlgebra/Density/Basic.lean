/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Basic.Real.Basic

/-!
# Densities on real vector spaces

A `Density V m` is a real-valued function on `m`-tuples transforming by the absolute
value of the determinant of an ambient linear endomorphism. In geometric applications,
`m` is the dimension of `V`: these are signed top-dimensional densities, with no chosen
orientation. They form a real vector space under pointwise operations.

Evaluation on a basis is a linear equivalence with ℝ. Its inverse sends a scalar `c`
to `v ↦ |b.det v| * c`. The evaluation and change-of-basis formulas include dimension
zero. In particular, a density vanishes on dependent tuples in positive dimension,
and a density is determined by its value on any one basis. This is the linear fibre
used for orientation-free integration and density-valued test sections.

The construction adapts Li Xuanji’s implementation in Tau Ceti PR #22145.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 16,
  Densities.
-/

public section

namespace TauCeti

/-- A top-dimensional density, expressed on `m`-tuples by the absolute determinant
transformation law. The top-dimensional case has `m = Module.finrank ℝ V`. Values may
be negative; positivity is not part of the carrier. -/
structure Density (V : Type*) [AddCommGroup V] [Module ℝ V] (m : ℕ) where
  /-- Evaluation on a tuple of vectors. -/
  toFun : (Fin m → V) → ℝ
  /-- Transformation under an ambient linear endomorphism. -/
  map_comp : ∀ (T : V →ₗ[ℝ] V) (v : Fin m → V),
    toFun (T ∘ v) = |LinearMap.det T| * toFun v

namespace Density

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {m : ℕ}

instance : FunLike (Density V m) (Fin m → V) ℝ where
  coe := toFun
  coe_injective μ ν h := by cases μ; cases ν; congr

@[ext]
theorem ext {μ ν : Density V m} (h : ∀ v, μ v = ν v) : μ = ν :=
  DFunLike.ext _ _ h

@[simp]
theorem coe_mk (f : (Fin m → V) → ℝ) (h) : (mk f h : (Fin m → V) → ℝ) = f := rfl

/-- The density transformation law in function-coercion notation. -/
theorem comp_apply (μ : Density V m) (T : V →ₗ[ℝ] V) (v : Fin m → V) :
    μ (T ∘ v) = |LinearMap.det T| * μ v := μ.map_comp T v

instance : Zero (Density V m) := ⟨⟨0, by simp⟩⟩

instance : Add (Density V m) := ⟨fun μ ν ↦
  ⟨μ + ν, fun T v ↦ by simp only [Pi.add_apply, comp_apply]; ring⟩⟩

instance : Neg (Density V m) := ⟨fun μ ↦
  ⟨-μ, fun T v ↦ by simp [comp_apply]⟩⟩

instance : Sub (Density V m) := ⟨fun μ ν ↦
  ⟨μ - ν, fun T v ↦ by simp only [Pi.sub_apply, comp_apply]; ring⟩⟩

instance {R : Type*} [SMul R ℝ] [SMulCommClass R ℝ ℝ] : SMul R (Density V m) :=
  ⟨fun c μ ↦ ⟨c • μ, fun T v ↦ by simp [comp_apply, mul_smul_comm]⟩⟩

@[simp]
theorem zero_apply (v : Fin m → V) : (0 : Density V m) v = 0 := rfl

@[simp]
theorem add_apply (μ ν : Density V m) (v : Fin m → V) : (μ + ν) v = μ v + ν v := rfl

@[simp]
theorem neg_apply (μ : Density V m) (v : Fin m → V) : (-μ) v = -μ v := rfl

@[simp]
theorem sub_apply (μ ν : Density V m) (v : Fin m → V) : (μ - ν) v = μ v - ν v := rfl

@[simp]
theorem smul_apply {R : Type*} [SMul R ℝ] [SMulCommClass R ℝ ℝ]
    (c : R) (μ : Density V m) (v : Fin m → V) : (c • μ) v = c • μ v := rfl

instance : AddCommGroup (Density V m) :=
  DFunLike.coe_injective.addCommGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance : Module ℝ (Density V m) :=
  Function.Injective.module ℝ ⟨⟨DFunLike.coe, rfl⟩, fun _ _ ↦ rfl⟩
    DFunLike.coe_injective (fun _ _ ↦ rfl)

/-- A density evaluated on an arbitrary tuple is its value on a basis multiplied by
the absolute determinant of that tuple. -/
theorem apply_eq_abs_det_mul (μ : Density V m) (b : Module.Basis (Fin m) ℝ V)
    (v : Fin m → V) : μ v = |b.det v| * μ b := by
  have hv : (b.constr ℝ v : V → V) ∘ b = v := by ext i; simp
  have hd : LinearMap.det (b.constr ℝ v) = b.det v := by
    simpa [hv, b.det_self] using (b.det_comp (b.constr ℝ v) b).symm
  calc
    μ v = μ ((b.constr ℝ v : V → V) ∘ b) := congrArg μ hv.symm
    _ = |b.det v| * μ b := by rw [comp_apply, hd]

/-- A density is zero exactly when its value on a basis is zero. -/
@[simp]
theorem apply_basis_eq_zero_iff (μ : Density V m) (b : Module.Basis (Fin m) ℝ V) :
    μ b = 0 ↔ μ = 0 :=
  ⟨fun h ↦ by
    ext v
    simp [Density.apply_eq_abs_det_mul μ b v, h], fun h ↦ by simp [h]⟩

end Density

end TauCeti

namespace Module.Basis

open TauCeti

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {m : ℕ}

/-- Agreement on one basis determines a density. -/
theorem density_ext (b : Module.Basis (Fin m) ℝ V) {μ ν : Density V m}
    (h : μ b = ν b) : μ = ν := by
  ext v
  simp only [Density.apply_eq_abs_det_mul _ b v, h]

/-- Construct a density with prescribed value `c` on a basis `b`. -/
noncomputable def density (b : Module.Basis (Fin m) ℝ V) (c : ℝ) : Density V m where
  toFun v := |b.det v| * c
  map_comp T v := by simp [abs_mul, mul_assoc]

@[simp]
theorem density_apply (b : Module.Basis (Fin m) ℝ V) (c : ℝ) (v : Fin m → V) :
    density b c v = |b.det v| * c := (rfl)

theorem density_apply_self (b : Module.Basis (Fin m) ℝ V) (c : ℝ) : density b c b = c := by
  simp [b.det_self]

/-- Evaluation on a basis identifies the real vector space of densities with ℝ. -/
noncomputable def densityEquiv (b : Module.Basis (Fin m) ℝ V) : Density V m ≃ₗ[ℝ] ℝ where
  toFun μ := μ b
  invFun := density b
  left_inv μ := b.density_ext (density_apply_self b (μ b))
  right_inv := density_apply_self b
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem densityEquiv_apply (b : Module.Basis (Fin m) ℝ V) (μ : Density V m) :
    densityEquiv b μ = μ b := (rfl)

@[simp]
theorem densityEquiv_symm_apply (b : Module.Basis (Fin m) ℝ V) (c : ℝ) :
    (densityEquiv b).symm c = density b c := (rfl)

/-- Changing the basis used to construct a density changes its scalar coefficient by
the absolute determinant. -/
theorem density_eq_density_mul (b b' : Module.Basis (Fin m) ℝ V) (c : ℝ) :
    density b c = density b' (|b.det b'| * c) := by
  apply b'.density_ext
  simp [b'.det_self]

/-- Top-dimensional densities form a one-dimensional vector space, including when
`V` itself has dimension zero. -/
theorem finrank_density (b : Module.Basis (Fin m) ℝ V) :
    Module.finrank ℝ (Density V m) = 1 := by
  rw [(densityEquiv b).finrank_eq, Module.finrank_self]

end Module.Basis

namespace TauCeti.Density

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {m : ℕ}

/-- The density fibre in the dimension of `V` is finite dimensional. -/
noncomputable instance [FiniteDimensional ℝ V] :
    FiniteDimensional ℝ (Density V (Module.finrank ℝ V)) :=
  (Module.finBasis ℝ V).densityEquiv.symm.finiteDimensional

/-- A top-dimensional density vanishes on a linearly dependent tuple. -/
theorem apply_eq_zero_of_not_linearIndependent (μ : Density V m)
    (b : Module.Basis (Fin m) ℝ V) {v : Fin m → V} (hv : ¬LinearIndependent ℝ v) :
    μ v = 0 := by
  have hd : b.det v = 0 := b.det.map_linearDependent v hv
  simp [apply_eq_abs_det_mul μ b v, hd]

/-- Pull back a density along a linear endomorphism of the ambient space. -/
def compLinearMap (μ : Density V m) (f : V →ₗ[ℝ] V) : Density V m where
  toFun v := μ (f ∘ v)
  map_comp T v := by
    -- Reassociate function composition so `μ.comp_apply` sees `f.comp T`.
    change μ ((f.comp T) ∘ v) = |LinearMap.det T| * μ (f ∘ v)
    rw [μ.comp_apply, LinearMap.det_comp, abs_mul, μ.comp_apply]
    ring

@[simp]
theorem compLinearMap_apply (μ : Density V m) (f : V →ₗ[ℝ] V) (v : Fin m → V) :
    μ.compLinearMap f v = μ (f ∘ v) := (rfl)

@[simp]
theorem compLinearMap_id (μ : Density V m) : μ.compLinearMap LinearMap.id = μ := by
  ext v
  rfl

/-- Pulling back along a composition of linear endomorphisms pulls back in reverse order. -/
theorem compLinearMap_comp (μ : Density V m) (f g : V →ₗ[ℝ] V) :
    μ.compLinearMap (f.comp g) = (μ.compLinearMap f).compLinearMap g := by
  ext v
  rfl

@[simp]
theorem compLinearMap_zero_left (f : V →ₗ[ℝ] V) :
    (0 : Density V m).compLinearMap f = 0 := by
  ext v
  rfl

@[simp]
theorem compLinearMap_add_left (μ ν : Density V m) (f : V →ₗ[ℝ] V) :
    (μ + ν).compLinearMap f = μ.compLinearMap f + ν.compLinearMap f := by
  ext v
  rfl

@[simp]
theorem compLinearMap_smul_left (c : ℝ) (μ : Density V m) (f : V →ₗ[ℝ] V) :
    (c • μ).compLinearMap f = c • μ.compLinearMap f := by
  ext v
  rfl

@[simp]
theorem compLinearMap_neg_left (μ : Density V m) (f : V →ₗ[ℝ] V) :
    (-μ).compLinearMap f = -μ.compLinearMap f := by
  ext v
  rfl

/-- Pull back a density along a linear equivalence between vector spaces. -/
def compLinearEquiv {W : Type*} [AddCommGroup W] [Module ℝ W]
    (μ : Density V m) (e : W ≃ₗ[ℝ] V) : Density W m where
  toFun w := μ (e ∘ w)
  map_comp T w := by
    have hconj : (e : W →ₗ[ℝ] V) ∘ (T ∘ w) =
        (((e : W →ₗ[ℝ] V) ∘ₗ T ∘ₗ (e.symm : V →ₗ[ℝ] W)) : V →ₗ[ℝ] V) ∘ (e ∘ w) := by
      ext i
      simp
    -- Coerce `e` to a linear map so `hconj` rewrites into an endomorphism of `V`.
    change μ ((e : W →ₗ[ℝ] V) ∘ (T ∘ w)) = |LinearMap.det T| * μ (e ∘ w)
    rw [hconj, μ.comp_apply, LinearMap.det_conj]

@[simp]
theorem compLinearEquiv_apply {W : Type*} [AddCommGroup W] [Module ℝ W]
    (μ : Density V m) (e : W ≃ₗ[ℝ] V) (w : Fin m → W) :
    μ.compLinearEquiv e w = μ (e ∘ w) := (rfl)

@[simp]
theorem compLinearEquiv_refl (μ : Density V m) :
    μ.compLinearEquiv (LinearEquiv.refl ℝ V) = μ := by
  ext v
  rfl

/-- Pulling back along a composition of linear equivalences pulls back in reverse order. -/
theorem compLinearEquiv_trans {U W : Type*} [AddCommGroup U] [Module ℝ U]
    [AddCommGroup W] [Module ℝ W] (μ : Density V m) (e₁ : U ≃ₗ[ℝ] W) (e₂ : W ≃ₗ[ℝ] V) :
    μ.compLinearEquiv (e₁.trans e₂) = (μ.compLinearEquiv e₂).compLinearEquiv e₁ := by
  ext u
  rfl

end TauCeti.Density

namespace AlternatingMap

open TauCeti Module

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {m : ℕ} [Fact (finrank ℝ V = m)]

/-- The orientation-free positive density `|φ|` of a top-degree alternating form `φ`, sending each
tuple `v` to `|φ v|`. -/
def absDensity (φ : V [⋀^Fin m]→ₗ[ℝ] ℝ) : Density V m where
  toFun v := |φ v|
  map_comp T v := by
    by_cases hm : m = 0
    · subst hm
      rw [LinearMap.det_eq_one_of_finrank_eq_zero Fact.out T, abs_one, one_mul,
        Subsingleton.elim (T ∘ v) v]
    · have hpos : 0 < finrank ℝ V := (Fact.out : finrank ℝ V = m).symm ▸ Nat.pos_of_ne_zero hm
      have : FiniteDimensional ℝ V := FiniteDimensional.of_finrank_pos hpos
      let b : Basis (Fin m) ℝ V := finBasisOfFinrankEq ℝ V Fact.out
      have h1 := DFunLike.congr_fun (φ.eq_smul_basis_det b) (T ∘ v)
      have h2 := DFunLike.congr_fun (φ.eq_smul_basis_det b) v
      simp only [smul_apply, smul_eq_mul, b.det_comp] at h1 h2
      rw [h1, h2, mul_left_comm, abs_mul]

@[simp]
theorem absDensity_apply (φ : V [⋀^Fin m]→ₗ[ℝ] ℝ) (v : Fin m → V) :
    φ.absDensity v = |φ v| := (rfl)

/-- The absolute density of an alternating form is everywhere nonnegative. -/
theorem absDensity_nonneg (φ : V [⋀^Fin m]→ₗ[ℝ] ℝ) (v : Fin m → V) :
    0 ≤ φ.absDensity v :=
  abs_nonneg (φ v)

@[simp]
theorem absDensity_zero : (0 : V [⋀^Fin m]→ₗ[ℝ] ℝ).absDensity = 0 := by
  ext v
  simp

@[simp]
theorem absDensity_neg (φ : V [⋀^Fin m]→ₗ[ℝ] ℝ) : (-φ).absDensity = φ.absDensity := by
  ext v
  simp

/-- Scaling an alternating form scales its absolute density by `|c|`. -/
theorem absDensity_smul (c : ℝ) (φ : V [⋀^Fin m]→ₗ[ℝ] ℝ) :
    (c • φ).absDensity = |c| • φ.absDensity := by
  ext v
  simp [abs_mul]

/-- The absolute density of a top-degree alternating form vanishes precisely when the form does. -/
@[simp]
theorem absDensity_eq_zero_iff (φ : V [⋀^Fin m]→ₗ[ℝ] ℝ) :
    φ.absDensity = 0 ↔ φ = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, absDensity_zero]⟩
  ext v
  exact abs_eq_zero.mp (DFunLike.congr_fun h v)

end AlternatingMap
