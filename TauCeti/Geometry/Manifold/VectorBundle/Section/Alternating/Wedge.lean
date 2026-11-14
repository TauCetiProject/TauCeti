/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Alternating.Wedge.ContinuousLinearMap
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Alternating.Basic
public import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Assoc

/-!
# Wedge products of alternating bundle sections

For a real vector bundle `V → M` and normed coefficient spaces `G₁`, `G₂`, `G₃` paired by a
continuous bilinear map `μ : G₁ →L[ℝ] G₂ →L[ℝ] G₃`, the fibrewise paired wedge
`ContinuousAlternatingMap.pairedWedge μ μ.continuous₂` sends `C^n` sections of
`fun x ↦ V x [⋀^Fin k]→L[ℝ] G₁` and `fun x ↦ V x [⋀^Fin l]→L[ℝ] G₂` to a `C^n` section of
`fun x ↦ V x [⋀^Fin (k + l)]→L[ℝ] G₃` (`ContMDiffSection.pairedWedge`). Read in a bundle
trivialization, precomposition commutes with `pairedWedge`, reducing regularity to the continuous
bilinear operator `ContinuousAlternatingMap.pairedWedgeCLM μ` on the fixed model fibre.

Specializing `μ` to multiplication on `ℝ` yields the scalar wedge product `ContMDiffSection.wedge`
on scalar-valued alternating sections, together with its bilinearity over smooth functions,
graded commutativity, associativity, and the degree-`-1` antiderivation law for
`ContMDiffSection.curryLeft`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer (2013), Chapter 14.
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace ContMDiffSection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {n : ℕ∞ω} {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]

/-! ### Paired wedge of alternating sections -/

section PairedWedge

variable {G₁ G₂ G₃ : Type*}
  [NormedAddCommGroup G₁] [NormedSpace ℝ G₁]
  [NormedAddCommGroup G₂] [NormedSpace ℝ G₂]
  [NormedAddCommGroup G₃] [NormedSpace ℝ G₃]
  {k l : ℕ}

/-- The fibrewise paired wedge of two `C^n` alternating bundle sections along a continuous bilinear
pairing `μ : G₁ →L[ℝ] G₂ →L[ℝ] G₃`. -/
def pairedWedge (μ : G₁ →L[ℝ] G₂ →L[ℝ] G₃)
    (φ : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] G₁, fun x ↦ V x [⋀^Fin k]→L[ℝ] G₁⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] G₂, fun x ↦ V x [⋀^Fin l]→L[ℝ] G₂⟯) :
    Cₛ^n⟮I; F [⋀^Fin (k + l)]→L[ℝ] G₃, fun x ↦ V x [⋀^Fin (k + l)]→L[ℝ] G₃⟯ where
  toFun x := ContinuousAlternatingMap.pairedWedge μ μ.continuous₂ (φ x) (ψ x)
  contMDiff_toFun x₀ := by
    rw [contMDiffAt_section_iff]
    have hφ := (contMDiffAt_section_iff x₀).1 (φ.contMDiff x₀)
    have hψ := (contMDiffAt_section_iff x₀).1 (ψ.contMDiff x₀)
    have heq :
        (fun x ↦ (trivializationAt (F [⋀^Fin (k + l)]→L[ℝ] G₃)
          (fun y ↦ V y [⋀^Fin (k + l)]→L[ℝ] G₃) x₀
          ⟨x, ContinuousAlternatingMap.pairedWedge μ μ.continuous₂ (φ x) (ψ x)⟩).2) =
        fun x ↦ ContinuousAlternatingMap.pairedWedgeCLM μ
          (trivializationAt (F [⋀^Fin k]→L[ℝ] G₁)
            (fun y ↦ V y [⋀^Fin k]→L[ℝ] G₁) x₀ ⟨x, φ x⟩).2
          (trivializationAt (F [⋀^Fin l]→L[ℝ] G₂)
            (fun y ↦ V y [⋀^Fin l]→L[ℝ] G₂) x₀ ⟨x, ψ x⟩).2 := by
      ext x v
      simp [FiberBundle.trivializationAt_continuousAlternatingMap_apply_snd,
        ContinuousAlternatingMap.pairedWedge_compContinuousLinearMap]
    rw [heq]
    exact ((contMDiffAt_const (c := ContinuousAlternatingMap.pairedWedgeCLM μ)).clm_apply
      hφ).clm_apply hψ

@[simp]
theorem pairedWedge_apply (μ : G₁ →L[ℝ] G₂ →L[ℝ] G₃)
    (φ : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] G₁, fun x ↦ V x [⋀^Fin k]→L[ℝ] G₁⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] G₂, fun x ↦ V x [⋀^Fin l]→L[ℝ] G₂⟯) (x : M) :
    pairedWedge μ φ ψ x = ContinuousAlternatingMap.pairedWedge μ μ.continuous₂ (φ x) (ψ x) :=
  (rfl)

end PairedWedge

/-! ### Scalar wedge product -/

section Wedge

variable {k l m : ℕ}

/-- The scalar wedge product `φ ∧ ψ` of two real-valued `C^n` alternating bundle sections. -/
def wedge
    (φ : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯) :
    Cₛ^n⟮I; F [⋀^Fin (k + l)]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin (k + l)]→L[ℝ] ℝ⟯ :=
  pairedWedge (ContinuousLinearMap.mul ℝ ℝ) φ ψ

theorem wedge_def
    (φ : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯) :
    φ.wedge ψ = pairedWedge (ContinuousLinearMap.mul ℝ ℝ) φ ψ :=
  (rfl)

@[simp]
theorem wedge_apply
    (φ : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯) (x : M) :
    φ.wedge ψ x =
      ContinuousAlternatingMap.pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
        (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (φ x) (ψ x) :=
  (rfl)

/-- Pointwise permutation-sum expansion of `ContMDiffSection.wedge`. -/
theorem wedge_apply_apply
    (φ : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯)
    (x : M) (v : Fin (k + l) → V x) :
    φ.wedge ψ x v =
      ((k.factorial : ℝ) * l.factorial)⁻¹ •
        ∑ σ : Equiv.Perm (Fin (k + l)), Equiv.Perm.sign σ •
          (φ x (fun i ↦ v (σ (Fin.castAdd l i))) * ψ x (fun j ↦ v (σ (Fin.natAdd k j)))) := by
  simpa [wedge_apply] using
    ContinuousAlternatingMap.pairedWedge_apply (ContinuousLinearMap.mul ℝ ℝ)
      (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (φ x) (ψ x) v

/-- Evaluating `φ.wedge ψ` on a tuple of `C^n` sections expresses the result in `C^n⟮I, M; ℝ⟯` as
the factorial-normalized signed sum of products of evaluations. -/
theorem evalSection_wedge
    (φ : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯)
    (s : Fin (k + l) → Cₛ^n⟮I; F, V⟯) :
    (φ.wedge ψ).evalSection s =
      ((k.factorial : ℝ) * l.factorial)⁻¹ •
        ∑ σ : Equiv.Perm (Fin (k + l)), Equiv.Perm.sign σ •
          (φ.evalSection (fun i ↦ s (σ (Fin.castAdd l i))) *
            ψ.evalSection (fun j ↦ s (σ (Fin.natAdd k j)))) := by
  ext x
  rw [evalSection_apply, wedge_apply_apply,
    ← ContMDiffMap.coeFnLinearMap_apply (𝕜 := ℝ), map_smul, map_sum]
  simp_rw [Units.smul_def, map_zsmul]
  simp only [Pi.smul_apply, Finset.sum_apply, ContMDiffMap.coeFnLinearMap_apply,
    ContMDiffMap.coe_mul, Pi.mul_apply, evalSection_apply]

theorem wedge_apply_zero_left
    (φ : Cₛ^n⟮I; F [⋀^Fin 0]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin 0]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯)
    (x : M) (v : Fin (0 + l) → V x) :
    φ.wedge ψ x v = φ x 0 * ψ x (v ∘ Fin.cast (Nat.zero_add l).symm) := by
  simp

@[simp]
theorem wedge_apply_zero_right
    (φ : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin 0]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin 0]→L[ℝ] ℝ⟯)
    (x : M) (v : Fin k → V x) :
    φ.wedge ψ x v = φ x v * ψ x 0 := by
  rw [wedge_apply]
  exact ContinuousAlternatingMap.pairedWedge_apply_zero_right (ContinuousLinearMap.mul ℝ ℝ)
    (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (φ x) (ψ x) v

theorem wedge_apply_one_one
    (φ ψ : Cₛ^n⟮I; F [⋀^Fin 1]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin 1]→L[ℝ] ℝ⟯)
    (x : M) (v w : V x) :
    φ.wedge ψ x ![v, w] = φ x ![v] * ψ x ![w] - φ x ![w] * ψ x ![v] := by
  rw [wedge_apply]
  exact ContinuousAlternatingMap.pairedWedge_apply_one_one
    (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (φ x) (ψ x) v w

@[simp]
theorem wedge_zero_left
    (ψ : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯) :
    (0 : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯).wedge ψ = 0 := by
  ext x v
  simp

@[simp]
theorem wedge_zero_right
    (φ : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯) :
    φ.wedge (0 : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯) = 0 := by
  ext x v
  simp

@[simp]
theorem wedge_add_left
    (φ₁ φ₂ : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯) :
    (φ₁ + φ₂).wedge ψ = φ₁.wedge ψ + φ₂.wedge ψ := by
  ext x v
  simp

@[simp]
theorem wedge_add_right
    (φ : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ₁ ψ₂ : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯) :
    φ.wedge (ψ₁ + ψ₂) = φ.wedge ψ₁ + φ.wedge ψ₂ := by
  ext x v
  simp

@[simp]
theorem wedge_smul_left (c : ℝ)
    (φ : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯) :
    (c • φ).wedge ψ = c • φ.wedge ψ := by
  ext x v
  simp

@[simp]
theorem wedge_smul_right (c : ℝ)
    (φ : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯) :
    φ.wedge (c • ψ) = c • φ.wedge ψ := by
  ext x v
  simp

@[simp]
theorem wedge_fun_smul_left (f : C^n⟮I, M; ℝ⟯)
    (φ : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯) :
    (f • φ).wedge ψ = f • φ.wedge ψ := by
  ext x v
  simp

@[simp]
theorem wedge_fun_smul_right (f : C^n⟮I, M; ℝ⟯)
    (φ : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯) :
    φ.wedge (f • ψ) = f • φ.wedge ψ := by
  ext x v
  simp

@[simp]
theorem wedge_neg_left
    (φ : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯) :
    (-φ).wedge ψ = -(φ.wedge ψ) := by
  rw [← neg_one_smul ℝ φ, wedge_smul_left, neg_one_smul ℝ (φ.wedge ψ)]

@[simp]
theorem wedge_neg_right
    (φ : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯) :
    φ.wedge (-ψ) = -(φ.wedge ψ) := by
  rw [← neg_one_smul ℝ ψ, wedge_smul_right, neg_one_smul ℝ (φ.wedge ψ)]

theorem wedge_sub_left
    (φ₁ φ₂ : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯) :
    (φ₁ - φ₂).wedge ψ = φ₁.wedge ψ - φ₂.wedge ψ := by
  rw [sub_eq_add_neg, wedge_add_left, wedge_neg_left, ← sub_eq_add_neg]

theorem wedge_sub_right
    (φ : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ₁ ψ₂ : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯) :
    φ.wedge (ψ₁ - ψ₂) = φ.wedge ψ₁ - φ.wedge ψ₂ := by
  rw [sub_eq_add_neg, wedge_add_right, wedge_neg_right, ← sub_eq_add_neg]

/-- **Graded commutativity** of the scalar wedge product, evaluated on fibre vectors. -/
theorem wedge_comm_apply
    (φ : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯)
    (x : M) (v : Fin (k + l) → V x) :
    φ.wedge ψ x v =
      (-1 : ℝ) ^ (k * l) • ψ.wedge φ x (v ∘ Fin.cast (Nat.add_comm l k)) :=
  ContinuousAlternatingMap.pairedWedge_comm (ContinuousLinearMap.mul ℝ ℝ).continuous₂
    (fun a b ↦ mul_comm a b) (φ x) (ψ x) v

/-- **Graded commutativity** of the scalar wedge product as an equality of sections. -/
theorem wedge_comm
    (φ : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯) :
    φ.wedge ψ =
      (-1 : ℝ) ^ (k * l) • LinearEquiv.cast (R := ℝ)
        (M := fun r : ℕ ↦ Cₛ^n⟮I; F [⋀^Fin r]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin r]→L[ℝ] ℝ⟯)
        (Nat.add_comm l k) (ψ.wedge φ) := by
  ext x v
  rw [ContMDiffSection.coe_smul, Pi.smul_apply, ContinuousAlternatingMap.smul_apply,
    cast_alternating_apply]
  exact wedge_comm_apply φ ψ x v

/-- **Associativity** of the scalar wedge product, evaluated on fibre vectors. -/
theorem wedge_assoc_apply
    (φ : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯)
    (θ : Cₛ^n⟮I; F [⋀^Fin m]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin m]→L[ℝ] ℝ⟯)
    (x : M) (v : Fin (k + l + m) → V x) :
    (φ.wedge ψ).wedge θ x v =
      φ.wedge (ψ.wedge θ) x (v ∘ Fin.cast (Nat.add_assoc k l m).symm) :=
  ContinuousAlternatingMap.pairedWedge_assoc
    (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ)
    (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ)
    (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (ContinuousLinearMap.mul ℝ ℝ).continuous₂
    (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (ContinuousLinearMap.mul ℝ ℝ).continuous₂
    (fun a b c : ℝ ↦ mul_assoc a b c) (φ x) (ψ x) (θ x) v

/-- **Associativity** of the scalar wedge product as an equality of sections. -/
theorem wedge_assoc
    (φ : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯)
    (θ : Cₛ^n⟮I; F [⋀^Fin m]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin m]→L[ℝ] ℝ⟯) :
    (φ.wedge ψ).wedge θ =
      LinearEquiv.cast (R := ℝ)
        (M := fun r : ℕ ↦ Cₛ^n⟮I; F [⋀^Fin r]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin r]→L[ℝ] ℝ⟯)
        (Nat.add_assoc k l m).symm (φ.wedge (ψ.wedge θ)) := by
  ext x v
  rw [cast_alternating_apply]
  exact wedge_assoc_apply φ ψ θ x v

theorem wedge_cast_left_apply {k' : ℕ} (h : k = k')
    (φ : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯)
    (x : M) (v : Fin (k' + l) → V x) :
    (LinearEquiv.cast (R := ℝ)
      (M := fun r : ℕ ↦ Cₛ^n⟮I; F [⋀^Fin r]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin r]→L[ℝ] ℝ⟯) h φ).wedge ψ
      x v = φ.wedge ψ x (v ∘ Fin.cast (by omega)) := by
  cases h
  simp

theorem wedge_cast_right_apply {l' : ℕ} (h : l = l')
    (φ : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯)
    (x : M) (v : Fin (k + l') → V x) :
    φ.wedge (LinearEquiv.cast (R := ℝ)
      (M := fun r : ℕ ↦ Cₛ^n⟮I; F [⋀^Fin r]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin r]→L[ℝ] ℝ⟯) h ψ)
      x v = φ.wedge ψ x (v ∘ Fin.cast (by omega)) := by
  cases h
  simp

/-! ### Interior product of a wedge -/

@[simp]
theorem curryLeft_wedge_zero_right
    (φ : Cₛ^n⟮I; F [⋀^Fin (k + 1)]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin (k + 1)]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin 0]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin 0]→L[ℝ] ℝ⟯)
    (a : Cₛ^n⟮I; F, V⟯) :
    (φ.wedge ψ).curryLeft a = (φ.curryLeft a).wedge ψ := by
  ext x w
  simp

@[simp]
theorem curryLeft_wedge_zero_left
    (φ : Cₛ^n⟮I; F [⋀^Fin 0]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin 0]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin (l + 1)]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin (l + 1)]→L[ℝ] ℝ⟯)
    (a : Cₛ^n⟮I; F, V⟯) :
    (φ.wedge ψ).curryLeft a = φ.wedge (ψ.curryLeft a) := by
  ext x w
  rw [curryLeft_apply_apply, wedge_apply_zero_left (l := l + 1),
    wedge_apply_zero_left (l := l), curryLeft_apply_apply]
  congr 2
  ext j
  cases j using Fin.cases <;> simp

/-- **Interior-product antiderivation law** for `ContMDiffSection.wedge`, evaluated on fibre
vectors: `ι_a (φ ∧ ψ) = ι_a φ ∧ ψ + (-1)^(k + 1) • φ ∧ ι_a ψ`. -/
theorem curryLeft_wedge_apply
    (φ : Cₛ^n⟮I; F [⋀^Fin (k + 1)]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin (k + 1)]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin (l + 1)]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin (l + 1)]→L[ℝ] ℝ⟯)
    (a : Cₛ^n⟮I; F, V⟯) (x : M) (w : Fin (k + 1 + l) → V x) :
    (φ.wedge ψ).curryLeft a x w =
      (φ.curryLeft a).wedge ψ x (w ∘ Fin.cast (show k + (l + 1) = k + 1 + l by omega)) +
        (-1 : ℝ) ^ (k + 1) • φ.wedge (ψ.curryLeft a) x w := by
  simp only [curryLeft_apply, wedge_apply]
  exact ContinuousAlternatingMap.curryLeftTopological_pairedWedge
    (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂
    (φ x) (ψ x) (a x) w

/-- **Interior-product antiderivation law** for `ContMDiffSection.wedge` as an equality of
sections. -/
theorem curryLeft_wedge
    (φ : Cₛ^n⟮I; F [⋀^Fin (k + 1)]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin (k + 1)]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin (l + 1)]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin (l + 1)]→L[ℝ] ℝ⟯)
    (a : Cₛ^n⟮I; F, V⟯) :
    (φ.wedge ψ).curryLeft a =
      LinearEquiv.cast (R := ℝ)
        (M := fun r : ℕ ↦ Cₛ^n⟮I; F [⋀^Fin r]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin r]→L[ℝ] ℝ⟯)
        (show k + (l + 1) = k + 1 + l by omega) ((φ.curryLeft a).wedge ψ) +
      (-1 : ℝ) ^ (k + 1) • φ.wedge (ψ.curryLeft a) := by
  ext x w
  rw [ContMDiffSection.coe_add, Pi.add_apply, ContinuousAlternatingMap.add_apply,
    cast_alternating_apply, ContMDiffSection.coe_smul, Pi.smul_apply,
    ContinuousAlternatingMap.smul_apply]
  exact curryLeft_wedge_apply φ ψ a x w

end Wedge

end ContMDiffSection
