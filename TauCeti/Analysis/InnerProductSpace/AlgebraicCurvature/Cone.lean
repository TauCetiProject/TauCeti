/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Cone.Basic
public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.ExteriorSquare
import TauCeti.Algebra.Order.BigOperators.Sum.PairwiseAdd
import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Dimension
import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Sectional
import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Basic
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Basic
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Compact
import TauCeti.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.Analysis.Normed.Module.HalfSpace

/-!
# Basic cones of algebraic curvature tensors

On a finite-dimensional real inner product space `V`, the basic curvature-positivity conditions,
which appear as curvature hypotheses in the convergence theorems of Hamilton and Böhm–Wilking for
the Ricci flow, cut out closed convex cones in the space `algebraicCurvatureSubmodule V` of
algebraic curvature tensors. Writing `R` for the bivector operator `curvatureEndomorphism r` of
`r`, this file defines, as `ProperCone ℝ` objects:

* `nonnegCurvatureOperatorCone V`: `⟪R ω, ω⟫ ≥ 0` for every bivector `ω`;
* `twoNonnegCurvatureOperatorCone V`: `⟪R ω₁, ω₁⟫ + ⟪R ω₂, ω₂⟫ ≥ 0` for every orthonormal pair of
  bivectors, that is, the two smallest eigenvalues of `R` have nonnegative sum;
* `nonnegSectionalCurvatureCone V`: `r(u, v, u, v) ≥ 0` for all `u, v` (this one needs no inner
  product, and is defined over any real normed space `V`);
* `nonnegRicciCone V`: `Ric(u, u) ≥ 0` for all `u`;
* `nonnegScalarCone V`: `Scal ≥ 0`.

Each is the intersection of the closed half-spaces of a family of continuous linear functionals of
the tensor. They are nested,

`nonnegCurvatureOperatorCone ≤ twoNonnegCurvatureOperatorCone ≤ nonnegRicciCone ≤ nonnegScalarCone`

and `nonnegCurvatureOperatorCone ≤ nonnegSectionalCurvatureCone ≤ nonnegRicciCone`, where the
inclusion of the 2-nonnegative cone in the Ricci cone needs `dim V ≠ 2`: in dimension two `⋀²V`
is a line, so every tensor is 2-nonnegative, while `-constantCurvature V` has negative Ricci
curvature. The constant-curvature tensor of the unit sphere has nonnegative curvature operator,
so by these inclusions it lies in all five cones, and the curvature-operator and sectional cones
are salient; outside dimension two so is the 2-nonnegative cone.

In finite dimensions each cone is cut out by a compact continuous family of linear inequalities,
so its interior is described by the corresponding strict inequalities: positive definite curvature
operator, 2-positive curvature operator, positive sectional curvature on linearly independent
pairs, positive definite Ricci contraction (outside dimension one) and positive scalar contraction
(in dimension at least two). The positive multiples of the round tensor lie in the interior of the
nonnegative-curvature-operator cone, hence in the interiors of all five cones, which therefore
have nonempty interior.

All five cones are invariant under the orthogonal group: for a linear isometric equivalence
`e : W ≃ₗᵢ[ℝ] V`, the preimage of each cone on `W` under the pullback
`algebraicCurvaturePullback e` is the corresponding cone on `V`. In particular, whether the
curvature tensor of a tangent space, transported to a model space by an orthonormal frame, lies in
one of these cones does not depend on the frame. Nonnegativity of the curvature operator and of
sectional curvature is preserved by pullback along every continuous linear map, so these two cones
are invariant under every continuous linear equivalence; 2-nonnegativity is preserved by pullback
along every linear isometric embedding.

## Main definitions

* `TauCeti.FourTensor.nonnegCurvatureOperatorCone`,
  `TauCeti.FourTensor.twoNonnegCurvatureOperatorCone`,
  `TauCeti.FourTensor.nonnegSectionalCurvatureCone`, `TauCeti.FourTensor.nonnegRicciCone`, and
  `TauCeti.FourTensor.nonnegScalarCone`.

## Main results

* `TauCeti.FourTensor.nonnegCurvatureOperatorCone_le_twoNonnegCurvatureOperatorCone`,
  `TauCeti.FourTensor.nonnegCurvatureOperatorCone_le_nonnegSectionalCurvatureCone`,
  `TauCeti.FourTensor.nonnegSectionalCurvatureCone_le_nonnegRicciCone`,
  `TauCeti.FourTensor.twoNonnegCurvatureOperatorCone_le_nonnegRicciCone`, and
  `TauCeti.FourTensor.nonnegRicciCone_le_nonnegScalarCone`: the inclusions.
* `TauCeti.FourTensor.comap_algebraicCurvaturePullback_nonnegCurvatureOperatorCone` and its
  analogues for the other four cones: orthogonal invariance.
* `TauCeti.FourTensor.salient_nonnegCurvatureOperatorCone`,
  `TauCeti.FourTensor.salient_nonnegSectionalCurvatureCone` and
  `TauCeti.FourTensor.salient_twoNonnegCurvatureOperatorCone`: these cones are salient, the last
  outside dimension two.
* `TauCeti.FourTensor.mem_interior_nonnegCurvatureOperatorCone`,
  `TauCeti.FourTensor.mem_interior_twoNonnegCurvatureOperatorCone`,
  `TauCeti.FourTensor.mem_interior_nonnegSectionalCurvatureCone`,
  `TauCeti.FourTensor.mem_interior_nonnegRicciCone` and
  `TauCeti.FourTensor.mem_interior_nonnegScalarCone`: the interiors are the strict conditions.
* `TauCeti.FourTensor.smul_constantCurvature_mem_interior_nonnegCurvatureOperatorCone`: the round
  ray lies in the interior.
* `TauCeti.FourTensor.comap_algebraicCurvaturePullback_eq_of_comp_eq_id`: a cone is invariant under
  pullback along an invertible map once pullback along the map and along its inverse preserve it.

## References

* R. S. Hamilton, *Four-manifolds with positive curvature operator*, J. Differential Geom. 24
  (1986), 153–179, Section 2.
* C. Böhm and B. Wilking, *Manifolds with positive curvature operators are space forms*,
  Ann. of Math. 167 (2008), 1079–1097, Section 2.
* P. Topping, *Lectures on the Ricci flow*, LMS Lecture Note Series 325, Cambridge University
  Press (2006), Chapter 9.
-/

public section

open scoped RealInnerProductSpace

noncomputable section

namespace TauCeti.FourTensor

section NormedSpace

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W]

/-! ### Invariance under invertible pullbacks -/

/-- A cone `C` on `V` is the preimage of a cone `D` on `W` under pullback along `f : W →L[ℝ] V` as
soon as `f` has a right inverse `g`, pullback along `f` maps `C` into `D`, and pullback along `g`
maps `D` into `C`. -/
theorem comap_algebraicCurvaturePullback_eq_of_comp_eq_id {f : W →L[ℝ] V} {g : V →L[ℝ] W}
    (hfg : f.comp g = .id ℝ V) {C : ProperCone ℝ (algebraicCurvatureSubmodule V)}
    {D : ProperCone ℝ (algebraicCurvatureSubmodule W)}
    (hf : ∀ r ∈ C, algebraicCurvaturePullback f r ∈ D)
    (hg : ∀ r ∈ D, algebraicCurvaturePullback g r ∈ C) :
    D.comap (algebraicCurvaturePullback f) = C := by
  ext r
  refine ⟨fun h ↦ ?_, hf r⟩
  rw [← algebraicCurvaturePullback_algebraicCurvaturePullback_of_comp_eq_id hfg r]
  exact hg _ h

/-! ### The sectional curvature cone -/

variable (V) in
/-- The cone of algebraic curvature tensors with nonnegative sectional curvature:
`r(u, v, u, v) ≥ 0` for all `u, v`. -/
def nonnegSectionalCurvatureCone : ProperCone ℝ (algebraicCurvatureSubmodule V) :=
  ⨅ (u : V) (v : V), (ProperCone.positive ℝ ℝ).comap
    ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 4 ↦ V) ℝ ![u, v, u, v]).comp
      (algebraicCurvatureSubmodule V).subtypeL)

@[simp]
theorem mem_nonnegSectionalCurvatureCone {r : algebraicCurvatureSubmodule V} :
    r ∈ nonnegSectionalCurvatureCone V ↔ ∀ u v, 0 ≤ r.val ![u, v, u, v] := by
  simp [nonnegSectionalCurvatureCone]

/-- The nonnegative-sectional-curvature cone is salient: it contains no line through the origin,
since an algebraic curvature tensor is determined by its sectional values. -/
theorem eq_zero_of_mem_nonnegSectionalCurvatureCone_of_neg_mem
    {r : algebraicCurvatureSubmodule V} (hr : r ∈ nonnegSectionalCurvatureCone V)
    (hr' : -r ∈ nonnegSectionalCurvatureCone V) : r = 0 := by
  have h₁ := mem_nonnegSectionalCurvatureCone.mp hr
  have h₂ := mem_nonnegSectionalCurvatureCone.mp hr'
  refine Subtype.ext ((mem_algebraicCurvatureSubmodule.mp r.property).eq_of_apply_self_eq
    (mem_algebraicCurvatureSubmodule.mp (algebraicCurvatureSubmodule V).zero_mem) fun u v ↦ ?_)
  have := h₂ u v
  simp only [NegMemClass.coe_neg, neg_apply] at this
  simp only [Submodule.coe_zero, zero_apply]
  exact le_antisymm (by linarith) (h₁ u v)

/-- The nonnegative-sectional-curvature cone is salient. -/
theorem salient_nonnegSectionalCurvatureCone :
    ConvexCone.Salient (R := ℝ) (G := algebraicCurvatureSubmodule V)
      (nonnegSectionalCurvatureCone V : ConvexCone ℝ _) :=
  fun _ hr hr₀ hr' ↦ hr₀ (eq_zero_of_mem_nonnegSectionalCurvatureCone_of_neg_mem hr hr')

/-- Pullback along any continuous linear map preserves nonnegativity of sectional curvature. -/
theorem algebraicCurvaturePullback_mem_nonnegSectionalCurvatureCone (f : W →L[ℝ] V)
    {r : algebraicCurvatureSubmodule V} (hr : r ∈ nonnegSectionalCurvatureCone V) :
    algebraicCurvaturePullback f r ∈ nonnegSectionalCurvatureCone W :=
  mem_nonnegSectionalCurvatureCone.mpr fun u v ↦ by
    rw [coe_algebraicCurvaturePullback, compContinuousLinearMap_apply_vec]
    exact mem_nonnegSectionalCurvatureCone.mp hr _ _

/-- Nonnegativity of sectional curvature is invariant under every continuous linear equivalence,
in particular under the orthogonal group. -/
theorem comap_algebraicCurvaturePullback_nonnegSectionalCurvatureCone (e : W ≃L[ℝ] V) :
    (nonnegSectionalCurvatureCone W).comap (algebraicCurvaturePullback (e : W →L[ℝ] V)) =
      nonnegSectionalCurvatureCone V :=
  comap_algebraicCurvaturePullback_eq_of_comp_eq_id (g := (e.symm : V →L[ℝ] W)) (by ext; simp)
    (fun _ ↦ algebraicCurvaturePullback_mem_nonnegSectionalCurvatureCone _)
    (fun _ ↦ algebraicCurvaturePullback_mem_nonnegSectionalCurvatureCone _)

end NormedSpace

section InnerProductSpace

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-! ### The defining functionals -/

/-- The value `⟪R ω, ω⟫` of the bivector operator of `r` on `ω`, as a continuous linear functional
of the algebraic curvature tensor `r`. -/
private def curvatureOperatorEvalL (ω : ⋀[ℝ]^2 V) : algebraicCurvatureSubmodule V →L[ℝ] ℝ :=
  (LinearMap.toContinuousLinearMap
    (innerₗ (⋀[ℝ]^2 V) ω ∘ₗ LinearMap.applyₗ ω ∘ₗ curvatureEndomorphism)).comp
      (algebraicCurvatureSubmodule V).subtypeL

private theorem curvatureOperatorEvalL_apply (ω : ⋀[ℝ]^2 V) (r : algebraicCurvatureSubmodule V) :
    curvatureOperatorEvalL ω r = ⟪curvatureEndomorphism r.val ω, ω⟫ := by
  simp [curvatureOperatorEvalL, real_inner_comm]

private theorem curvatureOperatorEvalL_smul (c : ℝ) (ω : ⋀[ℝ]^2 V) :
    curvatureOperatorEvalL (c • ω) = c ^ 2 • curvatureOperatorEvalL ω := by
  ext r
  simp only [curvatureOperatorEvalL_apply, map_smul, inner_smul_left, inner_smul_right,
    conj_trivial, smul_apply, smul_eq_mul]
  ring

/-! ### The cones -/

variable (V) in
/-- The cone of algebraic curvature tensors with nonnegative curvature operator:
`⟪R ω, ω⟫ ≥ 0` for every bivector `ω`, where `R = curvatureEndomorphism r`. -/
def nonnegCurvatureOperatorCone : ProperCone ℝ (algebraicCurvatureSubmodule V) :=
  ⨅ ω : ⋀[ℝ]^2 V, (ProperCone.positive ℝ ℝ).comap (curvatureOperatorEvalL ω)

@[simp]
theorem mem_nonnegCurvatureOperatorCone {r : algebraicCurvatureSubmodule V} :
    r ∈ nonnegCurvatureOperatorCone V ↔ ∀ ω, 0 ≤ ⟪curvatureEndomorphism r.val ω, ω⟫ := by
  simp [nonnegCurvatureOperatorCone, curvatureOperatorEvalL_apply]

variable (V) in
/-- The cone of algebraic curvature tensors with 2-nonnegative curvature operator:
`⟪R ω₁, ω₁⟫ + ⟪R ω₂, ω₂⟫ ≥ 0` for every orthonormal pair of bivectors `ω₁, ω₂`, where
`R = curvatureEndomorphism r`; equivalently, the two smallest eigenvalues of `R` have nonnegative
sum. When `⋀[ℝ]^2 V` has dimension at most one there is no orthonormal pair and the condition is
vacuous. -/
def twoNonnegCurvatureOperatorCone : ProperCone ℝ (algebraicCurvatureSubmodule V) :=
  ⨅ (ω : ⋀[ℝ]^2 V × ⋀[ℝ]^2 V) (_ : Orthonormal ℝ ![ω.fst, ω.snd]),
    (ProperCone.positive ℝ ℝ).comap (curvatureOperatorEvalL ω.fst + curvatureOperatorEvalL ω.snd)

@[simp]
theorem mem_twoNonnegCurvatureOperatorCone {r : algebraicCurvatureSubmodule V} :
    r ∈ twoNonnegCurvatureOperatorCone V ↔ ∀ ω₁ ω₂, Orthonormal ℝ ![ω₁, ω₂] →
      0 ≤ ⟪curvatureEndomorphism r.val ω₁, ω₁⟫ + ⟪curvatureEndomorphism r.val ω₂, ω₂⟫ := by
  simp [twoNonnegCurvatureOperatorCone, curvatureOperatorEvalL_apply]

variable (V) in
/-- The cone of algebraic curvature tensors with nonnegative Ricci contraction:
`Ric(u, u) ≥ 0` for all `u`. -/
def nonnegRicciCone : ProperCone ℝ (algebraicCurvatureSubmodule V) :=
  ⨅ u : V, (ProperCone.positive ℝ ℝ).comap
    ((LinearMap.toContinuousLinearMap (LinearMap.applyₗ u ∘ₗ LinearMap.applyₗ u ∘ₗ ricci)).comp
      (algebraicCurvatureSubmodule V).subtypeL)

@[simp]
theorem mem_nonnegRicciCone {r : algebraicCurvatureSubmodule V} :
    r ∈ nonnegRicciCone V ↔ ∀ u, 0 ≤ ricci r.val u u := by
  simp [nonnegRicciCone]

variable (V) in
/-- The cone of algebraic curvature tensors with nonnegative scalar contraction. -/
def nonnegScalarCone : ProperCone ℝ (algebraicCurvatureSubmodule V) :=
  (ProperCone.positive ℝ ℝ).comap
    ((LinearMap.toContinuousLinearMap scalar).comp (algebraicCurvatureSubmodule V).subtypeL)

@[simp]
theorem mem_nonnegScalarCone {r : algebraicCurvatureSubmodule V} :
    r ∈ nonnegScalarCone V ↔ 0 ≤ scalar r.val := by
  simp [nonnegScalarCone]

/-! ### Inclusions -/

/-- A nonnegative curvature operator is 2-nonnegative. -/
theorem nonnegCurvatureOperatorCone_le_twoNonnegCurvatureOperatorCone :
    nonnegCurvatureOperatorCone V ≤ twoNonnegCurvatureOperatorCone V := fun _ hr ↦
  mem_twoNonnegCurvatureOperatorCone.mpr fun ω₁ ω₂ _ ↦
    add_nonneg (mem_nonnegCurvatureOperatorCone.mp hr ω₁) (mem_nonnegCurvatureOperatorCone.mp hr ω₂)

/-- A nonnegative curvature operator has nonnegative sectional curvature: `r(u, v, u, v)` is the
value of the operator on the bivector `u ∧ v`. -/
theorem nonnegCurvatureOperatorCone_le_nonnegSectionalCurvatureCone :
    nonnegCurvatureOperatorCone V ≤ nonnegSectionalCurvatureCone V := fun r hr ↦
  mem_nonnegSectionalCurvatureCone.mpr fun u v ↦
    ((mem_algebraicCurvatureSubmodule.mp r.property).inner_curvatureEndomorphism_ιMulti u v u v) ▸
      mem_nonnegCurvatureOperatorCone.mp hr _

/-- Nonnegative sectional curvature implies nonnegative Ricci curvature:
`Ric(u, u) = ∑ᵢ r(eᵢ, u, eᵢ, u)`. -/
theorem nonnegSectionalCurvatureCone_le_nonnegRicciCone :
    nonnegSectionalCurvatureCone V ≤ nonnegRicciCone V := fun r hr ↦
  mem_nonnegRicciCone.mpr fun u ↦ by
    rw [ricci_apply_orthonormalBasis (stdOrthonormalBasis ℝ V)]
    exact Finset.sum_nonneg fun _ _ ↦ mem_nonnegSectionalCurvatureCone.mp hr _ _

/-- Nonnegative Ricci curvature implies nonnegative scalar curvature:
`Scal = ∑ᵢ Ric(eᵢ, eᵢ)`. -/
theorem nonnegRicciCone_le_nonnegScalarCone : nonnegRicciCone V ≤ nonnegScalarCone V :=
  fun r hr ↦ mem_nonnegScalarCone.mpr <| by
    rw [scalar_apply, bilinFormTrace_eq_sum _ (stdOrthonormalBasis ℝ V)]
    exact Finset.sum_nonneg fun _ _ ↦ mem_nonnegRicciCone.mp hr _

/-- On a unit vector `e`, 2-nonnegativity of the curvature operator gives `Ric(e, e) ≥ 0` unless
`dim V = 2`: in an orthonormal basis `(e, b₂, …, bₙ)`, `Ric(e, e) = ∑ⱼ ⟪R (e ∧ bⱼ), e ∧ bⱼ⟫` is
a sum of `n - 1 ≠ 1` terms, any two of which have nonnegative sum. -/
private theorem ricci_apply_self_nonneg_of_mem_twoNonneg (hn : Module.finrank ℝ V ≠ 2)
    {r : algebraicCurvatureSubmodule V} (hr : r ∈ twoNonnegCurvatureOperatorCone V) {e : V}
    (he : ‖e‖ = 1) : 0 ≤ ricci r.val e e := by
  have hR := mem_algebraicCurvatureSubmodule.mp r.property
  have hpos : 0 < Module.finrank ℝ V :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨e, norm_ne_zero_iff.mp (he.trans_ne one_ne_zero)⟩
  let i₀ : Fin (Module.finrank ℝ V) := ⟨0, hpos⟩
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℝ)
    (ι := Fin (Module.finrank ℝ V)) (by simp) (v := fun _ ↦ e) (s := {i₀}) <| by
      rw [orthonormal_iff_ite]
      rintro ⟨i, hi⟩ ⟨j, hj⟩
      simp only [Set.mem_singleton_iff] at hi hj
      subst hi hj
      simp [he]
  have hb₀ : b i₀ = e := hb i₀ rfl
  -- The `i₀` term `r(e, e, e, e)` vanishes by antisymmetry.
  have hself : r.val ![e, e, e, e] = 0 := by linarith [hR.antisymm_first e e e e]
  -- Each remaining term is the value of the operator on `e ∧ bⱼ`.
  have hterm (j : Fin (Module.finrank ℝ V)) :
      r.val ![b j, e, b j, e] =
        ⟪curvatureEndomorphism r.val (exteriorPower.ιMulti ℝ 2 ![e, b j]),
          exteriorPower.ιMulti ℝ 2 ![e, b j]⟫ := by
    rw [hR.inner_curvatureEndomorphism_ιMulti, hR.antisymm_first, hR.antisymm_last, neg_neg]
  rw [ricci_apply_orthonormalBasis b, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), hb₀,
    hself, zero_add]
  refine Finset.sum_nonneg_of_pairwise_add_nonneg ?_ fun i hi j hj hij ↦ ?_
  · rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  · rw [hterm, hterm]
    have hi₀ := Finset.ne_of_mem_erase hi
    have hj₀ := Finset.ne_of_mem_erase hj
    rw [← hb₀]
    refine mem_twoNonnegCurvatureOperatorCone.mp hr _ _
      (exteriorPower.orthonormal_ιMulti_two_of_orthonormal ?_)
    rw [orthonormal_iff_ite]
    intro a c
    fin_cases a <;> fin_cases c <;>
      simp [b.inner_eq_ite, hi₀.symm, hj₀.symm, hij, hi₀, hj₀, hij.symm]

/-- Outside dimension two, a 2-nonnegative curvature operator has nonnegative Ricci curvature.
In dimension two every tensor is 2-nonnegative, so the inclusion fails there. -/
theorem twoNonnegCurvatureOperatorCone_le_nonnegRicciCone (hn : Module.finrank ℝ V ≠ 2) :
    twoNonnegCurvatureOperatorCone V ≤ nonnegRicciCone V := fun r hr ↦
  mem_nonnegRicciCone.mpr fun u ↦ by
    rcases eq_or_ne u 0 with rfl | hu
    · simp
    have hu' : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
    have h := ricci_apply_self_nonneg_of_mem_twoNonneg hn hr (e := ‖u‖⁻¹ • u) <| by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hu']
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, ← mul_assoc] at h
    exact (mul_nonneg_iff_of_pos_left
      (mul_self_pos.mpr (inv_ne_zero hu'))).mp h

/-! ### The round tensor and salience -/

/-- The constant-curvature tensor of the unit sphere, whose curvature operator is the identity,
has nonnegative curvature operator. -/
theorem constantCurvature_mem_nonnegCurvatureOperatorCone :
    (⟨constantCurvature V, mem_algebraicCurvatureSubmodule.mpr
      isAlgebraicCurvature_constantCurvature⟩ :
      algebraicCurvatureSubmodule V) ∈ nonnegCurvatureOperatorCone V :=
  mem_nonnegCurvatureOperatorCone.mpr fun _ ↦ by simp

/-- The nonnegative-curvature-operator cone is salient: it contains no line through the origin. An
algebraic curvature tensor whose curvature operator has vanishing quadratic form is zero, since the
operator is symmetric. -/
theorem eq_zero_of_mem_nonnegCurvatureOperatorCone_of_neg_mem {r : algebraicCurvatureSubmodule V}
    (hr : r ∈ nonnegCurvatureOperatorCone V) (hr' : -r ∈ nonnegCurvatureOperatorCone V) :
    r = 0 := by
  have h₁ := mem_nonnegCurvatureOperatorCone.mp hr
  have h₂ := mem_nonnegCurvatureOperatorCone.mp hr'
  refine curvatureEndomorphismEquiv.injective (Subtype.ext ?_)
  have hsymm := (mem_algebraicCurvatureSubmodule.mp r.property).isSymmetric_curvatureEndomorphism
  rw [coe_curvatureEndomorphismEquiv, map_zero, Submodule.coe_zero, ← hsymm.inner_map_self_eq_zero]
  intro ω
  have := h₂ ω
  simp only [NegMemClass.coe_neg, map_neg, LinearMap.neg_apply, inner_neg_left] at this
  exact le_antisymm (by linarith) (h₁ ω)

/-- The nonnegative-curvature-operator cone is salient. -/
theorem salient_nonnegCurvatureOperatorCone :
    ConvexCone.Salient (R := ℝ) (G := algebraicCurvatureSubmodule V)
      (nonnegCurvatureOperatorCone V : ConvexCone ℝ _) :=
  fun _ hr hr₀ hr' ↦ hr₀ (eq_zero_of_mem_nonnegCurvatureOperatorCone_of_neg_mem hr hr')

/-- Outside dimension two, the 2-nonnegative cone contains no line through the origin: if `r` and
`-r` are both 2-nonnegative, then `r = 0`. The hypothesis is needed: in dimension two, where
`⋀[ℝ]^2 V` is a line, every tensor is 2-nonnegative and the cone is the whole space. -/
theorem eq_zero_of_mem_twoNonnegCurvatureOperatorCone_of_neg_mem (hn : Module.finrank ℝ V ≠ 2)
    {r : algebraicCurvatureSubmodule V} (hr : r ∈ twoNonnegCurvatureOperatorCone V)
    (hr' : -r ∈ twoNonnegCurvatureOperatorCone V) : r = 0 := by
  classical
  rcases le_or_gt (Module.finrank ℝ V) 1 with h1 | h1
  · exact Subtype.ext (eq_zero_of_finrank_le_one_of_antisymm_first h1
      (mem_algebraicCurvatureSubmodule.mp r.property).antisymm_first)
  replace hn : 3 ≤ Module.finrank ℝ V := by omega
  have h₁ := mem_twoNonnegCurvatureOperatorCone.mp hr
  have h₂ := mem_twoNonnegCurvatureOperatorCone.mp hr'
  simp only [NegMemClass.coe_neg, map_neg, LinearMap.neg_apply, inner_neg_left] at h₂
  have hdim : 2 < Module.finrank ℝ (⋀[ℝ]^2 V) := by
    rw [exteriorPower.finrank_eq]
    exact (by decide : 2 < Nat.choose 3 2).trans_le (Nat.choose_le_choose 2 hn)
  -- In dimension at least three, the values `aᵢ = ⟪R ωᵢ, ωᵢ⟫` on an orthonormal triple of
  -- bivectors satisfy `aᵢ + aⱼ = 0` for `i ≠ j`, so they vanish. Every unit bivector `ω` lies in
  -- such a triple `ω, ω₂, ω₃`, so the quadratic form of `R` vanishes on unit bivectors.
  have hunit (ω : ⋀[ℝ]^2 V) (hω : ω ∈ Metric.sphere 0 1) : curvatureOperatorEvalL ω r = 0 := by
    rw [mem_sphere_zero_iff_norm] at hω
    rw [curvatureOperatorEvalL_apply]
    obtain ⟨ω₂, hω₂, hω₂o⟩ := exists_norm_eq_one_forall_inner_eq_zero_of_card_lt_finrank (𝕜 := ℝ)
      ({ω} : Finset _) (by rw [Finset.card_singleton]; omega)
    obtain ⟨ω₃, hω₃, hω₃o⟩ := exists_norm_eq_one_forall_inner_eq_zero_of_card_lt_finrank (𝕜 := ℝ)
      ({ω, ω₂} : Finset _) (Finset.card_le_two.trans_lt hdim)
    have h₁₂ : ⟪ω, ω₂⟫ = 0 := hω₂o ω (by simp)
    have h₁₃ : ⟪ω, ω₃⟫ = 0 := hω₃o ω (by simp)
    have h₂₃ : ⟪ω₂, ω₃⟫ = 0 := hω₃o ω₂ (by simp)
    have hpair {a b : ⋀[ℝ]^2 V} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : ⟪a, b⟫ = 0) :
        Orthonormal ℝ ![a, b] := by
      simp [orthonormal_vecCons_iff, ha, hb, hab]
    linarith [h₁ _ _ (hpair hω hω₂ h₁₂), h₂ _ _ (hpair hω hω₂ h₁₂), h₁ _ _ (hpair hω hω₃ h₁₃),
      h₂ _ _ (hpair hω hω₃ h₁₃), h₁ _ _ (hpair hω₂ hω₃ h₂₃), h₂ _ _ (hpair hω₂ hω₃ h₂₃)]
  -- By homogeneity, `r` and `-r` then have nonnegative curvature operator.
  have hmem (s : algebraicCurvatureSubmodule V)
      (hs : ∀ ω ∈ Metric.sphere (0 : ⋀[ℝ]^2 V) 1, 0 ≤ curvatureOperatorEvalL ω s) :
      s ∈ nonnegCurvatureOperatorCone V :=
    mem_nonnegCurvatureOperatorCone.mpr fun ω ↦ by
      simpa only [curvatureOperatorEvalL_apply] using (Set.ext_iff.mp
        (setOf_forall_mem_sphere_nonneg_apply (φ := curvatureOperatorEvalL (V := V))
          curvatureOperatorEvalL_smul) s).mp hs ω
  exact eq_zero_of_mem_nonnegCurvatureOperatorCone_of_neg_mem
    (hmem r fun ω hω ↦ (hunit ω hω).ge) (hmem (-r) fun ω hω ↦ by
      have := (curvatureOperatorEvalL ω).map_neg r
      rw [hunit ω hω, neg_zero] at this
      exact this.ge)

/-- Outside dimension two, the 2-nonnegative cone is salient. -/
theorem salient_twoNonnegCurvatureOperatorCone (hn : Module.finrank ℝ V ≠ 2) :
    ConvexCone.Salient (R := ℝ) (G := algebraicCurvatureSubmodule V)
      (twoNonnegCurvatureOperatorCone V : ConvexCone ℝ _) :=
  fun _ hr hr₀ hr' ↦ hr₀ (eq_zero_of_mem_twoNonnegCurvatureOperatorCone_of_neg_mem hn hr hr')

/-! ### Orthogonal invariance -/

/-- Pullback along any continuous linear map preserves nonnegativity of the curvature operator:
the pulled-back operator evaluates the original one on the image bivector. -/
theorem algebraicCurvaturePullback_mem_nonnegCurvatureOperatorCone (f : W →L[ℝ] V)
    {r : algebraicCurvatureSubmodule V} (hr : r ∈ nonnegCurvatureOperatorCone V) :
    algebraicCurvaturePullback f r ∈ nonnegCurvatureOperatorCone W :=
  mem_nonnegCurvatureOperatorCone.mpr fun ω ↦ by
    rw [coe_algebraicCurvaturePullback, f.inner_curvatureEndomorphism_compContinuousLinearMap]
    exact mem_nonnegCurvatureOperatorCone.mp hr _

/-- Pullback along a linear isometric embedding preserves 2-nonnegativity of the curvature
operator, since the induced map on bivectors preserves orthonormal pairs. -/
theorem algebraicCurvaturePullback_mem_twoNonnegCurvatureOperatorCone (f : W →ₗᵢ[ℝ] V)
    {r : algebraicCurvatureSubmodule V} (hr : r ∈ twoNonnegCurvatureOperatorCone V) :
    algebraicCurvaturePullback f.toContinuousLinearMap r ∈ twoNonnegCurvatureOperatorCone W :=
  mem_twoNonnegCurvatureOperatorCone.mpr fun ω₁ ω₂ hω ↦ by
    let F : ⋀[ℝ]^2 W →ₗᵢ[ℝ] ⋀[ℝ]^2 V :=
      (exteriorPower.map 2 f.toLinearMap).isometryOfInner (exteriorPower.inner_map_map f)
    simp only [coe_algebraicCurvaturePullback,
      ContinuousLinearMap.inner_curvatureEndomorphism_compContinuousLinearMap]
    refine mem_twoNonnegCurvatureOperatorCone.mp hr _ _ ?_
    convert hω.comp_linearIsometry F using 1
    ext i
    fin_cases i <;> simp [F]

/-- Nonnegativity of the curvature operator is invariant under every continuous linear
equivalence, in particular under the orthogonal group. -/
theorem comap_algebraicCurvaturePullback_nonnegCurvatureOperatorCone (e : W ≃L[ℝ] V) :
    (nonnegCurvatureOperatorCone W).comap (algebraicCurvaturePullback (e : W →L[ℝ] V)) =
      nonnegCurvatureOperatorCone V :=
  comap_algebraicCurvaturePullback_eq_of_comp_eq_id (g := (e.symm : V →L[ℝ] W)) (by ext; simp)
    (fun _ ↦ algebraicCurvaturePullback_mem_nonnegCurvatureOperatorCone _)
    (fun _ ↦ algebraicCurvaturePullback_mem_nonnegCurvatureOperatorCone _)

/-- The 2-nonnegative-curvature-operator cone is invariant under linear isometric
equivalences. -/
theorem comap_algebraicCurvaturePullback_twoNonnegCurvatureOperatorCone (e : W ≃ₗᵢ[ℝ] V) :
    (twoNonnegCurvatureOperatorCone W).comap
        (algebraicCurvaturePullback e.toLinearIsometry.toContinuousLinearMap) =
      twoNonnegCurvatureOperatorCone V :=
  comap_algebraicCurvaturePullback_eq_of_comp_eq_id
    (g := e.symm.toLinearIsometry.toContinuousLinearMap) (by ext; simp)
    (fun _ ↦ algebraicCurvaturePullback_mem_twoNonnegCurvatureOperatorCone _)
    (fun _ ↦ algebraicCurvaturePullback_mem_twoNonnegCurvatureOperatorCone _)

/-- The nonnegative-Ricci cone is invariant under linear isometric equivalences. -/
theorem comap_algebraicCurvaturePullback_nonnegRicciCone (e : W ≃ₗᵢ[ℝ] V) :
    (nonnegRicciCone W).comap
        (algebraicCurvaturePullback e.toLinearIsometry.toContinuousLinearMap) =
      nonnegRicciCone V := by
  ext r
  simp only [ProperCone.mem_comap, mem_nonnegRicciCone, coe_algebraicCurvaturePullback,
    ricci_compContinuousLinearMap_linearIsometryEquiv]
  exact (e.surjective.forall (p := fun u ↦ 0 ≤ ricci r.val u u)).symm

/-- The nonnegative-scalar cone is invariant under linear isometric equivalences. -/
theorem comap_algebraicCurvaturePullback_nonnegScalarCone (e : W ≃ₗᵢ[ℝ] V) :
    (nonnegScalarCone W).comap
        (algebraicCurvaturePullback e.toLinearIsometry.toContinuousLinearMap) =
      nonnegScalarCone V := by
  ext r
  simp only [ProperCone.mem_comap, mem_nonnegScalarCone, coe_algebraicCurvaturePullback,
    scalar_compContinuousLinearMap_linearIsometryEquiv]

/-! ### Interiors -/

/-- The constant-curvature tensor of the unit sphere, as an element of
`algebraicCurvatureSubmodule V`. -/
private abbrev roundTensor : algebraicCurvatureSubmodule V :=
  ⟨constantCurvature V, mem_algebraicCurvatureSubmodule.mpr isAlgebraicCurvature_constantCurvature⟩

/-- An algebraic curvature tensor lies in the interior of the nonnegative-curvature-operator cone
exactly when its curvature operator is positive definite. -/
@[simp]
theorem mem_interior_nonnegCurvatureOperatorCone {r : algebraicCurvatureSubmodule V} :
    r ∈ interior (nonnegCurvatureOperatorCone V : Set (algebraicCurvatureSubmodule V)) ↔
      ∀ ω, ω ≠ 0 → 0 < ⟪curvatureEndomorphism r.val ω, ω⟫ := by
  have hset : (nonnegCurvatureOperatorCone V : Set (algebraicCurvatureSubmodule V)) =
      {q | ∀ ω, 0 ≤ curvatureOperatorEvalL ω q} := by
    ext q
    simp only [SetLike.mem_coe, mem_nonnegCurvatureOperatorCone, Set.mem_ofPred_eq,
      curvatureOperatorEvalL_apply]
  rw [hset, interior_setOf_forall_nonneg_apply (E := algebraicCurvatureSubmodule V)
    (continuous_clm_apply.mpr fun q ↦ by
      simp only [curvatureOperatorEvalL_apply]
      exact (LinearMap.continuous_of_finiteDimensional _).inner continuous_id)
    curvatureOperatorEvalL_smul
    fun ω hω h ↦ hω (by simpa [curvatureOperatorEvalL_apply] using congr($h roundTensor))]
  simp only [Set.mem_ofPred_eq, curvatureOperatorEvalL_apply]

/-- An algebraic curvature tensor lies in the interior of the 2-nonnegative cone exactly when its
curvature operator is 2-positive: `⟪R ω₁, ω₁⟫ + ⟪R ω₂, ω₂⟫ > 0` for every orthonormal pair of
bivectors, that is, the two smallest eigenvalues of `R` have positive sum. When `⋀[ℝ]^2 V` has
dimension at most one both sides hold for every tensor. -/
@[simp]
theorem mem_interior_twoNonnegCurvatureOperatorCone {r : algebraicCurvatureSubmodule V} :
    r ∈ interior (twoNonnegCurvatureOperatorCone V : Set (algebraicCurvatureSubmodule V)) ↔
      ∀ ω₁ ω₂, Orthonormal ℝ ![ω₁, ω₂] →
        0 < ⟪curvatureEndomorphism r.val ω₁, ω₁⟫ + ⟪curvatureEndomorphism r.val ω₂, ω₂⟫ := by
  set φ : (Fin 2 → ⋀[ℝ]^2 V) → algebraicCurvatureSubmodule V →L[ℝ] ℝ :=
    fun ω ↦ curvatureOperatorEvalL (ω 0) + curvatureOperatorEvalL (ω 1)
  have hset : (twoNonnegCurvatureOperatorCone V : Set (algebraicCurvatureSubmodule V)) =
      {q | ∀ ω ∈ {ω : Fin 2 → ⋀[ℝ]^2 V | Orthonormal ℝ ω}, 0 ≤ φ ω q} := by
    ext q
    simp only [SetLike.mem_coe, mem_twoNonnegCurvatureOperatorCone, Set.mem_ofPred_eq, φ,
      add_apply, curvatureOperatorEvalL_apply]
    exact ⟨fun h ω hω ↦ h _ _ (hω.pair zero_ne_one), fun h ω₁ ω₂ hω ↦ by simpa using h _ hω⟩
  rw [hset, interior_setOf_forall_mem_nonneg_apply (E := algebraicCurvatureSubmodule V)
    isCompact_setOfPred_orthonormal
    (continuousOn_clm_apply.mpr fun q ↦ by
      have hR : Continuous fun ω : ⋀[ℝ]^2 V ↦ ⟪curvatureEndomorphism q.val ω, ω⟫ :=
        (LinearMap.continuous_of_finiteDimensional _).inner continuous_id
      simp only [φ, add_apply, curvatureOperatorEvalL_apply]
      exact ((hR.comp (continuous_apply 0)).add (hR.comp (continuous_apply 1))).continuousOn)
    fun ω hω h ↦ by
      have := congr($h roundTensor)
      simp only [φ, add_apply, curvatureOperatorEvalL_apply,
        curvatureEndomorphism_constantCurvature, LinearMap.id_apply, real_inner_self_eq_norm_sq,
        hω.1, zero_apply] at this
      norm_num at this]
  simp only [Set.mem_ofPred_eq, φ, add_apply, curvatureOperatorEvalL_apply]
  exact ⟨fun h ω₁ ω₂ hω ↦ by simpa using h _ hω, fun h ω hω ↦ h _ _ (hω.pair zero_ne_one)⟩

/-- An algebraic curvature tensor lies in the interior of the nonnegative-sectional-curvature cone
exactly when its sectional curvature is positive: `r(u, v, u, v) > 0` for every linearly
independent pair `u, v`. -/
@[simp]
theorem mem_interior_nonnegSectionalCurvatureCone {r : algebraicCurvatureSubmodule V} :
    r ∈ interior (nonnegSectionalCurvatureCone V : Set (algebraicCurvatureSubmodule V)) ↔
      ∀ u v, LinearIndependent ℝ ![u, v] → 0 < r.val ![u, v, u, v] := by
  set φ : (Fin 2 → V) → algebraicCurvatureSubmodule V →L[ℝ] ℝ := fun f ↦
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 4 ↦ V) ℝ ![f 0, f 1, f 0, f 1]).comp
      (algebraicCurvatureSubmodule V).subtypeL
  -- On a linearly independent pair, `r(u, v, u, v)` is a positive multiple of the value of `r` on
  -- an orthonormal pair.
  have hgram (q : algebraicCurvatureSubmodule V) {u v : V} (huv : LinearIndependent ℝ ![u, v]) :
      ∃ e₀ e₁ : V, Orthonormal ℝ ![e₀, e₁] ∧ ∃ c : ℝ, 0 < c ∧
        q.val ![u, v, u, v] = c * q.val ![e₀, e₁, e₀, e₁] := by
    obtain ⟨e₀, e₁, he, -, -, heq⟩ :=
      (mem_algebraicCurvatureSubmodule.mp q.property).exists_orthonormal_apply_self_eq_det_gram_mul
        huv
    exact ⟨e₀, e₁, he, _, (Matrix.posDef_gram_of_linearIndependent huv).det_pos, heq⟩
  have hset : (nonnegSectionalCurvatureCone V : Set (algebraicCurvatureSubmodule V)) =
      {q | ∀ f ∈ {f : Fin 2 → V | Orthonormal ℝ f}, 0 ≤ φ f q} := by
    ext q
    simp only [SetLike.mem_coe, mem_nonnegSectionalCurvatureCone, Set.mem_ofPred_eq, φ,
      ContinuousLinearMap.coe_comp, Function.comp_apply, Submodule.subtypeL_apply,
      ContinuousMultilinearMap.apply_apply]
    refine ⟨fun h f _ ↦ h _ _, fun h u v ↦ ?_⟩
    by_cases huv : LinearIndependent ℝ ![u, v]
    · obtain ⟨e₀, e₁, he, c, hc, heq⟩ := hgram q huv
      rw [heq]
      exact mul_nonneg hc.le (by simpa using h _ he)
    · rw [(mem_algebraicCurvatureSubmodule.mp
        q.property).apply_self_eq_zero_of_not_linearIndependent huv]
  rw [hset, interior_setOf_forall_mem_nonneg_apply (E := algebraicCurvatureSubmodule V)
    isCompact_setOfPred_orthonormal
    (continuousOn_clm_apply.mpr fun q ↦ (q.val.cont.comp (continuous_pi fun k ↦ by
      fin_cases k <;> exact continuous_apply _)).continuousOn)
    fun f hf h ↦ by
      have := congr($h roundTensor)
      simp only [φ, ContinuousLinearMap.coe_comp, Function.comp_apply, Submodule.subtypeL_apply,
        ContinuousMultilinearMap.apply_apply, constantCurvature_apply_self, hf.1,
        hf.2 zero_ne_one, zero_apply] at this
      norm_num at this]
  simp only [Set.mem_ofPred_eq, φ, ContinuousLinearMap.coe_comp, Function.comp_apply,
    Submodule.subtypeL_apply, ContinuousMultilinearMap.apply_apply]
  refine ⟨fun h u v huv ↦ ?_, fun h f hf ↦ h _ _ (hf.pair zero_ne_one).linearIndependent⟩
  obtain ⟨e₀, e₁, he, c, hc, heq⟩ := hgram r huv
  rw [heq]
  exact mul_pos hc (by simpa using h _ he)

/-- Outside dimension one, an algebraic curvature tensor lies in the interior of the
nonnegative-Ricci cone exactly when its Ricci contraction is positive definite. In dimension one
the only algebraic curvature tensor is zero, which lies in the interior but has vanishing Ricci
contraction. -/
theorem mem_interior_nonnegRicciCone (hn : Module.finrank ℝ V ≠ 1)
    {r : algebraicCurvatureSubmodule V} :
    r ∈ interior (nonnegRicciCone V : Set (algebraicCurvatureSubmodule V)) ↔
      ∀ u, u ≠ 0 → 0 < ricci r.val u u := by
  set φ : V → algebraicCurvatureSubmodule V →L[ℝ] ℝ := fun u ↦
    (LinearMap.toContinuousLinearMap (LinearMap.applyₗ u ∘ₗ LinearMap.applyₗ u ∘ₗ ricci)).comp
      (algebraicCurvatureSubmodule V).subtypeL
  have hφ_apply (u : V) (q : algebraicCurvatureSubmodule V) : φ u q = ricci q.val u u := by
    simp [φ]
  have hset : (nonnegRicciCone V : Set (algebraicCurvatureSubmodule V)) =
      {q | ∀ u, 0 ≤ φ u q} := by
    ext q
    simp only [SetLike.mem_coe, mem_nonnegRicciCone, Set.mem_ofPred_eq, hφ_apply]
  rw [hset, interior_setOf_forall_nonneg_apply (E := algebraicCurvatureSubmodule V)
    (continuous_clm_apply.mpr fun q ↦ by
      simp only [hφ_apply, ricci_apply_orthonormalBasis (stdOrthonormalBasis ℝ V)]
      exact continuous_finsetSum _ fun i _ ↦ q.val.cont.comp (by fun_prop))
    (fun c u ↦ by
      ext q
      simp only [hφ_apply, map_smul, LinearMap.smul_apply, smul_apply, smul_eq_mul]
      ring)
    fun u hu h ↦ by
      have := congr($h roundTensor)
      simp only [hφ_apply, ricci_constantCurvature, LinearMap.smul_apply, innerₗ_apply_apply,
        real_inner_self_eq_norm_sq, smul_eq_mul, zero_apply, mul_eq_zero, sub_eq_zero,
        pow_eq_zero_iff two_ne_zero, norm_eq_zero] at this
      exact this.elim (fun h1 ↦ hn (by exact_mod_cast h1)) hu]
  simp only [Set.mem_ofPred_eq, hφ_apply]

/-- In dimension at least two, an algebraic curvature tensor lies in the interior of the
nonnegative-scalar cone exactly when its scalar contraction is positive. In dimension at most one
the only algebraic curvature tensor is zero, which lies in the interior. -/
theorem mem_interior_nonnegScalarCone (hn : 2 ≤ Module.finrank ℝ V)
    {r : algebraicCurvatureSubmodule V} :
    r ∈ interior (nonnegScalarCone V : Set (algebraicCurvatureSubmodule V)) ↔
      0 < scalar r.val := by
  set φ : Unit → algebraicCurvatureSubmodule V →L[ℝ] ℝ := fun _ ↦
    (LinearMap.toContinuousLinearMap scalar).comp (algebraicCurvatureSubmodule V).subtypeL
  have hset : (nonnegScalarCone V : Set (algebraicCurvatureSubmodule V)) =
      {q | ∀ i ∈ (Set.univ : Set Unit), 0 ≤ φ i q} := by
    ext q
    simp [φ]
  rw [hset, interior_setOf_forall_mem_nonneg_apply (E := algebraicCurvatureSubmodule V)
    isCompact_univ continuousOn_const
    fun _ _ h ↦ by
      have := congr($h roundTensor)
      simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, Submodule.subtypeL_apply,
        LinearMap.coe_toContinuousLinearMap', scalar_constantCurvature,
        zero_apply] at this
      have h2 : (2 : ℝ) ≤ Module.finrank ℝ V := by exact_mod_cast hn
      nlinarith]
  simp

/-- Every positive multiple of the constant-curvature tensor of the unit sphere lies in the
interior of the nonnegative-curvature-operator cone. Since this cone is contained in the other
four basic cones, `interior_mono` places the round ray in each of their interiors as well. -/
theorem smul_constantCurvature_mem_interior_nonnegCurvatureOperatorCone {κ : ℝ} (hκ : 0 < κ) :
    (⟨κ • constantCurvature V, Submodule.smul_mem _ κ (mem_algebraicCurvatureSubmodule.mpr
      isAlgebraicCurvature_constantCurvature)⟩ : algebraicCurvatureSubmodule V) ∈
      interior (nonnegCurvatureOperatorCone V : Set (algebraicCurvatureSubmodule V)) :=
  mem_interior_nonnegCurvatureOperatorCone.mpr fun ω hω ↦ by
    simp only [map_smul, curvatureEndomorphism_constantCurvature, LinearMap.smul_apply,
      LinearMap.id_apply, real_inner_smul_left, real_inner_self_eq_norm_sq]
    exact mul_pos hκ (pow_pos (norm_pos_iff.mpr hω) 2)

end InnerProductSpace

end TauCeti.FourTensor
