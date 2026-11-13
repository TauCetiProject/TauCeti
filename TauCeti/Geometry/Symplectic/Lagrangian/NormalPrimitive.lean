/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
public import TauCeti.Geometry.Symplectic.Lagrangian.TotallyReal
public import TauCeti.Geometry.Symplectic.Liouville.Linear
public import TauCeti.LinearAlgebra.TotallyReal.CompatibleForm

/-!
# The normal primitive of a maximal totally real subspace

Let `J` be an almost complex structure on a real vector space `V` and `L` a maximal totally real
subspace, so that every vector is uniquely `x = a + ν` with `a ∈ L` and `ν ∈ J L`. Write `P` for
the projection onto `L` along `J L`, and let `g` be a bilinear form, positive on `L`. The one-form
field

`β_x(ζ) = g(P (J x), P ζ)`

depends only on the normal component `ν = x - P x` of the base point: it is `g(J ν, P ζ)`, the
pairing of `-J⁻¹ ν` with the tangential part of `ζ`. It vanishes along `L`, and its exterior
derivative is the constant two-form

`σ(v, w) = β_v(w) - β_w(v)`.

This form tames `J`, since `σ(v, J v) = g(P v, P v) + g(P (J v), P (J v))`, and `L` is Lagrangian
for it. When `g` is symmetric on `L`, `σ` is moreover `J`-invariant and its metric `σ(·, J ·)` is
the `J`-invariant extension of `g` constructed in
`TauCeti.LinearAlgebra.TotallyReal.CompatibleForm`, for which `J L` is the orthogonal complement
of `L`. With respect to that metric `β` is bounded by
the distance to `L`: `β_x(ζ)² ≤ |x - a|² |ζ|²` for every `a ∈ L`.

So a maximal totally real subspace is Lagrangian for a symplectic form compatible with `J`, and on
a finite-dimensional space this characterizes maximal totally real subspaces. This is the converse
of `TauCeti.SymplecticForm.IsLagrangian.isMaximalTotallyReal_of_compatible`.

The form `β` is the linear model of the primitive used in the removal of boundary singularities of
holomorphic curves with totally real boundary: on the `J`-normal tube `y + ν` around a totally
real submanifold, with `ν ∈ J T_y L`, McDuff and Salamon use `β_(y,ν)(ζ) = -g(J⁻¹ ν, dπ ζ)`. Its
differential tames `J` near `L`, it vanishes on `T L`, and it is bounded by the distance to `L`.
In the linear model, with `J` constant and `L` a linear subspace, these properties hold on the
whole space, and `L` is Lagrangian for `σ` although it need not be Lagrangian for any form given in
advance.

## Main definitions

* `TauCeti.IsMaximalTotallyReal.normalPrimitive`: the bilinear form `(x, ζ) ↦ β_x(ζ)`.
* `TauCeti.IsMaximalTotallyReal.symplecticForm`: the symplectic form `σ = dβ`.
* `TauCeti.IsMaximalTotallyReal.normalPrimitiveForm`: on a finite-dimensional normed space, `β` as
  a differential one-form.

## Main results

* `TauCeti.IsMaximalTotallyReal.normalPrimitive_apply_of_mem`: `β` vanishes along `L`.
* `TauCeti.IsMaximalTotallyReal.normalPrimitive_eq_compatibleForm`: `β_x(ζ)` is the metric pairing
  of `J (x - P x)` with `ζ`.
* `TauCeti.IsMaximalTotallyReal.sq_normalPrimitive_apply_le`: `β_x(ζ)² ≤ |x - a|² |ζ|²` for every
  `a ∈ L`.
* `TauCeti.IsMaximalTotallyReal.symplecticForm_tames`,
  `TauCeti.IsMaximalTotallyReal.symplecticForm_compatible`,
  `TauCeti.IsMaximalTotallyReal.isLagrangian_symplecticForm` and
  `TauCeti.IsMaximalTotallyReal.associatedBilinForm_symplecticForm`: `σ` tames `J`, is compatible
  with `J` when `g` is symmetric on `L`, makes `L` Lagrangian, and has metric the compatible form
  of `g`.
* `TauCeti.isMaximalTotallyReal_iff_exists_compatible_isLagrangian`: on a finite-dimensional space,
  `L` is maximal totally real exactly when it is Lagrangian for some symplectic form compatible
  with `J`.
* `TauCeti.IsMaximalTotallyReal.extDeriv_normalPrimitiveForm_apply`: `dβ = σ`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52** (2012), Chapter 4 (the primitive on a tube around a totally real
  submanifold, in the removal of boundary singularities) and Appendix C.1.
-/

public section

noncomputable section

namespace TauCeti

namespace IsMaximalTotallyReal

section Algebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {J : AlmostComplexStructure V}
  {L : Submodule ℝ V} (hL : IsMaximalTotallyReal J.toLinearMap L) (g : LinearMap.BilinForm ℝ V)

/-- The normal primitive `β_x(ζ) = g(P (J x), P ζ)` of a maximal totally real subspace `L`, where
`P` is the projection onto `L` along `J L`. It vanishes for `x ∈ L`, and `β_v(w) - β_w(v)` is the
symplectic form `TauCeti.IsMaximalTotallyReal.symplecticForm`. -/
def normalPrimitive : LinearMap.BilinForm ℝ V :=
  g.compl₁₂ (L.projection (L.map J.toLinearMap) hL.isCompl ∘ₗ J.toLinearMap)
    (L.projection (L.map J.toLinearMap) hL.isCompl)

/-- Evaluation of the normal primitive. -/
@[simp]
theorem normalPrimitive_apply (x ζ : V) :
    hL.normalPrimitive g x ζ =
      g (L.projection (L.map J.toLinearMap) hL.isCompl (J x))
        (L.projection (L.map J.toLinearMap) hL.isCompl ζ) := by
  simp [normalPrimitive]

/-- The normal primitive vanishes along `L`. -/
theorem normalPrimitive_apply_of_mem {x : V} (hx : x ∈ L) (ζ : V) :
    hL.normalPrimitive g x ζ = 0 := by
  rw [normalPrimitive_apply, hL.projection_map_of_mem hx, map_zero, LinearMap.zero_apply]

/-- The normal primitive vanishes on the normal directions `J L`. -/
theorem normalPrimitive_apply_map_of_mem (x : V) {b : V} (hb : b ∈ L) :
    hL.normalPrimitive g x (J b) = 0 := by
  rw [normalPrimitive_apply, hL.projection_map_of_mem hb, map_zero]

/-- The normal primitive is the pairing of `J ν` with `ζ` for the compatible form of `g`, where
`ν = x - P x` is the normal component of `x`. Since `J ν = -J⁻¹ ν`, this is the formula
`β_x(ζ) = -g(J⁻¹ ν, P ζ)`. -/
theorem normalPrimitive_eq_compatibleForm (x ζ : V) :
    hL.normalPrimitive g x ζ =
      hL.compatibleForm g (J (x - L.projection (L.map J.toLinearMap) hL.isCompl x)) ζ := by
  set P := L.projection (L.map J.toLinearMap) hL.isCompl
  -- `x - P x = -J (P (J x))`, so `J (x - P x) = P (J x)`.
  have hx : x - P x = -J (P (J x)) := by
    nth_rw 1 [← hL.sub_map_projection_map J.square_neg x]
    exact sub_sub_cancel_left _ _
  rw [hx, map_neg, AlmostComplexStructure.apply_apply, neg_neg,
    hL.compatibleForm_apply_of_mem g (L.projection_apply_mem hL.isCompl _), normalPrimitive_apply]

/-- The normal primitive is bounded by the distance to `L` for the compatible form of `g`:
`β_x(ζ)² ≤ |x - a|² |ζ|²` for every `a ∈ L`. -/
theorem sq_normalPrimitive_apply_le (hg : ∀ a ∈ L, 0 ≤ g a a)
    (hsymm : ∀ a ∈ L, ∀ b ∈ L, g a b = g b a) {a : V}
    (ha : a ∈ L) (x ζ : V) :
    hL.normalPrimitive g x ζ ^ 2 ≤
      hL.compatibleForm g (x - a) (x - a) * hL.compatibleForm g ζ ζ := by
  set P := L.projection (L.map J.toLinearMap) hL.isCompl
  have hPmem (v : V) : P v ∈ L := L.projection_apply_mem hL.isCompl v
  -- Cauchy–Schwarz for the compatible form of `g`, applied to `P (J x)` and `P ζ` in `L`.
  have hCS := LinearMap.BilinForm.apply_sq_le_of_symm (hL.compatibleForm g)
    (fun v ↦ by
      rw [compatibleForm_apply]
      exact add_nonneg (hg _ (hPmem _)) (hg _ (hPmem _)))
    (LinearMap.BilinForm.isSymm_iff.1 (hL.isSymm_compatibleForm hsymm)) (P (J x)) (P ζ)
  rw [hL.compatibleForm_apply_of_mem_of_mem g (hPmem _) (hPmem _),
    hL.compatibleForm_apply_of_mem_of_mem g (hPmem _) (hPmem _),
    hL.compatibleForm_apply_of_mem_of_mem g (hPmem _) (hPmem _)] at hCS
  have hPJa : P (J (x - a)) = P (J x) := by
    rw [AlmostComplexStructure.apply_sub, map_sub, hL.projection_map_of_mem ha, sub_zero]
  have h₁ : g (P (J x)) (P (J x)) ≤ hL.compatibleForm g (x - a) (x - a) := by
    rw [compatibleForm_apply, hPJa]
    exact le_add_of_nonneg_left (hg _ (hPmem _))
  have h₂ : g (P ζ) (P ζ) ≤ hL.compatibleForm g ζ ζ := by
    rw [compatibleForm_apply]
    exact le_add_of_nonneg_right (hg _ (hPmem _))
  rw [normalPrimitive_apply]
  exact hCS.trans (mul_le_mul h₁ h₂ (hg _ (hPmem _)) ((hg _ (hPmem _)).trans h₁))

/-- The alternation of the normal primitive on `(v, J v)` is the compatible form of `g` on `v`. -/
theorem normalPrimitive_apply_sub_normalPrimitive_apply (v : V) :
    hL.normalPrimitive g v (J v) - hL.normalPrimitive g (J v) v = hL.compatibleForm g v v := by
  simp only [normalPrimitive_apply, compatibleForm_apply, AlmostComplexStructure.apply_apply,
    map_neg, LinearMap.neg_apply, sub_neg_eq_add]
  exact add_comm _ _

variable {g}

/-- The symplectic form `σ(v, w) = β_v(w) - β_w(v)` of a maximal totally real subspace, for a
bilinear form `g` positive on `L`; here `β` is `TauCeti.IsMaximalTotallyReal.normalPrimitive`.
It tames `J` and makes `L` Lagrangian, and it is the exterior derivative of `β`
(`TauCeti.IsMaximalTotallyReal.extDeriv_normalPrimitiveForm_apply`). -/
def symplecticForm (hg : ∀ a ∈ L, a ≠ 0 → 0 < g a a) : SymplecticForm V :=
  -- `σ(v, J v)` is the compatible form of `g` on `v`, positive for `v ≠ 0`.
  SymplecticForm.ofTames (J := J) (hL.normalPrimitive g - LinearMap.flip (hL.normalPrimitive g))
    (fun v ↦ by simp) fun v hv ↦ by
      simpa only [LinearMap.sub_apply, LinearMap.flip_apply,
        normalPrimitive_apply_sub_normalPrimitive_apply] using
        hL.compatibleForm_pos J.square_neg hg hv

variable (hg : ∀ a ∈ L, a ≠ 0 → 0 < g a a)

/-- Evaluation of the symplectic form of `L`: `σ(v, w) = β_v(w) - β_w(v)`. -/
@[simp]
theorem symplecticForm_apply (v w : V) :
    hL.symplecticForm hg v w = hL.normalPrimitive g v w - hL.normalPrimitive g w v :=
  -- `simp` cannot rewrite with `ofTames_apply` here: the stored alternation proof has the unfolded
  -- type `∀ v, σ v v = 0`, which does not match `IsAlt` at reducible transparency.
  (SymplecticForm.ofTames_apply _ _ v w).trans (by simp)

/-- The symplectic form of `L` evaluates on `(v, J v)` to the compatible form of `g`. -/
theorem symplecticForm_apply_map_self (v : V) :
    hL.symplecticForm hg v (J v) = hL.compatibleForm g v v := by
  rw [symplecticForm_apply, normalPrimitive_apply_sub_normalPrimitive_apply]

/-- The symplectic form of `L` tames `J`. -/
theorem symplecticForm_tames : (hL.symplecticForm hg).Tames J := fun v hv ↦ by
  rw [symplecticForm_apply_map_self]
  exact hL.compatibleForm_pos J.square_neg hg hv

/-- `L` is Lagrangian for its symplectic form. -/
theorem isLagrangian_symplecticForm : (hL.symplecticForm hg).IsLagrangian L := by
  set P := L.projection (L.map J.toLinearMap) hL.isCompl
  refine SymplecticForm.isLagrangian_iff.2 ⟨SymplecticForm.isIsotropic_iff.2 fun a ha b hb ↦ ?_,
    SymplecticForm.isCoisotropic_iff.2 fun v hv ↦ ?_⟩
  · simp [hL.normalPrimitive_apply_of_mem g ha, hL.normalPrimitive_apply_of_mem g hb]
  · -- Pairing `v` with `P (J v) ∈ L` gives `-g (P (J v)) (P (J v))`, so `P (J v) = 0`.
    have hPJ : P (J v) ∈ L := L.projection_apply_mem hL.isCompl _
    have h := SymplecticForm.mem_orthogonal_iff.1 hv _ hPJ
    rw [symplecticForm_apply, hL.normalPrimitive_apply_of_mem g hPJ, zero_sub, neg_eq_zero,
      normalPrimitive_apply, Submodule.projection_apply_of_mem_left hL.isCompl hPJ] at h
    have h0 : P (J v) = 0 := by
      by_contra hne
      exact (hg _ hPJ hne).ne' h
    obtain ⟨c, hc, hcv⟩ := (Submodule.projection_apply_eq_zero_iff hL.isCompl).1 h0
    rwa [← J.injective hcv]

variable {hg}

/-- When `g` is symmetric on `L`, the metric `σ(·, J ·)` of the symplectic form of `L` is the
compatible form of `g`, the `J`-invariant extension of `g` for which `J L` is orthogonal to `L`. -/
theorem associatedBilinForm_symplecticForm (hsymm : ∀ a ∈ L, ∀ b ∈ L, g a b = g b a) :
    (hL.symplecticForm hg).associatedBilinForm J = hL.compatibleForm g := by
  ext v w
  simp only [SymplecticForm.associatedBilinForm_apply, symplecticForm_apply, normalPrimitive_apply,
    compatibleForm_apply, AlmostComplexStructure.apply_apply, map_neg, LinearMap.neg_apply,
    sub_neg_eq_add]
  rw [hsymm _ (L.projection_apply_mem hL.isCompl w) _ (L.projection_apply_mem hL.isCompl v)]
  exact add_comm _ _

/-- When `g` is symmetric on `L`, the symplectic form of `L` is `J`-invariant. -/
theorem symplecticForm_invariant (hsymm : ∀ a ∈ L, ∀ b ∈ L, g a b = g b a) :
    (hL.symplecticForm hg).Invariant J := by
  refine (SymplecticForm.invariant_iff _ _).2 fun v w ↦ ?_
  simp only [symplecticForm_apply, normalPrimitive_apply, AlmostComplexStructure.apply_apply,
    map_neg, LinearMap.neg_apply]
  rw [hsymm _ (L.projection_apply_mem hL.isCompl v) _ (L.projection_apply_mem hL.isCompl (J w)),
    hsymm _ (L.projection_apply_mem hL.isCompl w) _ (L.projection_apply_mem hL.isCompl (J v))]
  ring

/-- When `g` is symmetric on `L`, the symplectic form of `L` is compatible with `J`. -/
theorem symplecticForm_compatible (hsymm : ∀ a ∈ L, ∀ b ∈ L, g a b = g b a) :
    (hL.symplecticForm hg).Compatible J :=
  .of_tames (hL.symplecticForm_invariant hsymm) (hL.symplecticForm_tames hg)

include hL in
/-- A maximal totally real subspace of a finite-dimensional space is Lagrangian for some symplectic
form compatible with `J`. -/
theorem exists_compatible_isLagrangian [FiniteDimensional ℝ V] :
    ∃ ω : SymplecticForm V, ω.Compatible J ∧ ω.IsLagrangian L := by
  -- Any inner product on `V` will do; take the dot product in a basis.
  let e := (Module.finBasis ℝ V).equivFun
  let g : LinearMap.BilinForm ℝ V := (Matrix.toBilin' 1).compl₁₂ e.toLinearMap e.toLinearMap
  have hge (v w : V) : g v w = e v ⬝ᵥ e w := by simp [g, Matrix.toBilin'_apply']
  have hsymm (v : V) (_ : v ∈ L) (w : V) (_ : w ∈ L) : g v w = g w v := by
    rw [hge, hge, dotProduct_comm]
  have hpos : ∀ a ∈ L, a ≠ 0 → 0 < g a a := fun a _ ha ↦ by
    rw [hge]
    exact lt_of_le_of_ne (Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _)
      (Ne.symm ((not_congr dotProduct_self_eq_zero).2 ((LinearEquiv.map_ne_zero_iff e).2 ha)))
  exact ⟨hL.symplecticForm hpos, hL.symplecticForm_compatible hsymm,
    hL.isLagrangian_symplecticForm hpos⟩

end Algebra

section Normed

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {J : AlmostComplexStructure V} {L : Submodule ℝ V} (hL : IsMaximalTotallyReal J.toLinearMap L)
  (g : LinearMap.BilinForm ℝ V)

/-- The normal primitive `TauCeti.IsMaximalTotallyReal.normalPrimitive` of `L` on a
finite-dimensional normed space, as a differential one-form: a continuous linear function of the
base point with values in continuous alternating one-forms. -/
def normalPrimitiveForm : V →L[ℝ] V [⋀^Fin 1]→L[ℝ] ℝ :=
  -- The radial one-form `x ↦ B(x, ·) / 2` of `B = 2 β` is `β`.
  ContinuousLinearMap.liouvilleFormCLM ((2 : ℝ) • (hL.normalPrimitive g).toContinuousBilinearMap)

/-- Evaluation of the normal primitive as a differential one-form. -/
@[simp]
theorem normalPrimitiveForm_apply (x : V) (v : Fin 1 → V) :
    hL.normalPrimitiveForm g x v = hL.normalPrimitive g x (v 0) := by
  simp [normalPrimitiveForm]

variable {g} in
/-- **The symplectic form of `L` is the exterior derivative of the normal primitive**:
`dβ = σ`. -/
theorem extDeriv_normalPrimitiveForm_apply
    (hg : ∀ a ∈ L, a ≠ 0 → 0 < g a a) (x : V) (v : Fin 2 → V) :
    extDeriv (hL.normalPrimitiveForm g) x v = hL.symplecticForm hg (v 0) (v 1) := by
  rw [normalPrimitiveForm, ContinuousLinearMap.extDeriv_liouvilleFormCLM_apply]
  simp [← mul_sub]

end Normed

end IsMaximalTotallyReal

/-- On a finite-dimensional space, a subspace is maximal totally real for `J` exactly when it is
Lagrangian for some symplectic form compatible with `J`. -/
theorem isMaximalTotallyReal_iff_exists_compatible_isLagrangian {V : Type*} [AddCommGroup V]
    [Module ℝ V] [FiniteDimensional ℝ V] {J : AlmostComplexStructure V} {L : Submodule ℝ V} :
    IsMaximalTotallyReal J.toLinearMap L ↔
      ∃ ω : SymplecticForm V, ω.Compatible J ∧ ω.IsLagrangian L :=
  ⟨fun hL ↦ hL.exists_compatible_isLagrangian, fun ⟨_, hω, hL⟩ ↦
    hL.isMaximalTotallyReal_of_compatible hω⟩

end TauCeti
