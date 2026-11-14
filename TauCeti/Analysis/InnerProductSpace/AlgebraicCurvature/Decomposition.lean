/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Trace
public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Operator
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.LinearCombination
import TauCeti.LinearAlgebra.Multilinear.CurvatureDimThree

/-!
# The Ricci–Weyl decomposition of algebraic curvature tensors

On a finite-dimensional real inner product space `V` of dimension `n`, every algebraic curvature
tensor `r` decomposes into three canonically defined, `O(V)`-equivariant, pairwise orthogonal
algebraic curvature components:

`r = scalarPart r + tracelessRicciPart r + weyl r`,

corresponding to the irreducible `O(V)`-summands of `algebraicCurvatureSubmodule V` when `n ≥ 4`:

* `scalarPart r = (scalar r / (n (n - 1))) • constantCurvature V` carries the scalar contraction
  and acts on `⋀[ℝ]^2 V` as `(scalar r / (n (n - 1))) • Id`.
* `tracelessRicciPart r = (n - 2)⁻¹ • kulkarniNomizu (tracelessRicci r) (innerₗ V)` carries the
  trace-free Ricci contraction `tracelessRicci r = ricci r - (scalar r / n) • innerₗ V` and acts on
  `⋀[ℝ]^2 V` as `(2 / (n - 2)) • wedgeEnd (tracelessRicciEnd r) Id`.
* `weyl r = r - scalarPart r - tracelessRicciPart r` is the completely trace-free *Weyl part* of
  `r`: for every algebraic curvature tensor `r` in every dimension `n`, `ricci (weyl r) = 0` and
  `scalar (weyl r) = 0`. Away from dimension `2`, `scalarPart r + tracelessRicciPart r` equals the
  Kulkarni–Nomizu product `kulkarniNomizu (schouten r) (innerₗ V)` of the *Schouten bilinear form*
  `schouten r = (n - 2)⁻¹ • (ricci r - (scalar r / (2 (n - 1))) • innerₗ V)` with the inner
  product, so `weyl r = r - kulkarniNomizu (schouten r) (innerₗ V)`.

In dimension `n ≤ 3`, the Weyl part of every algebraic curvature tensor vanishes identically
(`IsAlgebraicCurvature.weyl_eq_zero_of_finrank_le_three`), so curvature is completely determined by
its Ricci contraction (`r = scalarPart r + tracelessRicciPart r`).

Contracting a Kulkarni–Nomizu product `h ⊙ g` against any skew-pair four-tensor `q` in an
orthonormal basis `(bᵢ)` is adjoint to the Ricci contraction up to the combinatorial factor `4`:

`∑ i j k l, (h ⊙ g)(bᵢ, bⱼ, bₖ, bₗ) q(bᵢ, bⱼ, bₖ, bₗ) = 4 ∑ i k, h(bᵢ, bₖ) Ric(q)(bᵢ, bₖ)`.

Consequently `scalarPart r`, `tracelessRicciPart r`, and `weyl r` are pairwise orthogonal for the
component inner product in every orthonormal basis, yielding the Pythagorean identity
(`IsAlgebraicCurvature.sum_sq_eq_scalar_add_tracelessRicci_add_weyl`):

`∑ |r|² = (2 / (n (n - 1))) Scal(r)² + (4 / (n - 2)) ∑ |Ric₀(r)|² + ∑ |Weyl(r)|²`.

## Main definitions

* `TauCeti.FourTensor.ricciEnd`: the Ricci endomorphism on `V`, characterized by
  `⟪ricciEnd r u, v⟫ = ricci r u v`.
* `TauCeti.FourTensor.tracelessRicci`, `TauCeti.FourTensor.tracelessRicciEnd`: the trace-free Ricci
  bilinear form `Ric - (Scal / n) g` and its Riesz endomorphism `RicEnd - (Scal / n) Id`.
* `TauCeti.FourTensor.scalarPart`, `TauCeti.FourTensor.tracelessRicciPart`,
  `TauCeti.FourTensor.schouten`, `TauCeti.FourTensor.weyl`: the scalar, trace-free Ricci, Schouten,
  and Weyl maps.

## Main statements

* `TauCeti.FourTensor.curvatureOperator_scalarPart`,
  `TauCeti.FourTensor.IsAlgebraicCurvature.curvatureOperator_tracelessRicciPart`,
  `TauCeti.FourTensor.IsAlgebraicCurvature.curvatureOperator_eq`: bivector curvature operator
  identifications in terms of `LinearMap.id` and `TauCeti.wedgeEnd`.
* `TauCeti.FourTensor.IsAlgebraicCurvature.ricci_weyl`,
  `TauCeti.FourTensor.IsAlgebraicCurvature.scalar_weyl`,
  `TauCeti.FourTensor.weyl_weyl`: trace-freeness and idempotence of `weyl`
  across all dimensions.
* `TauCeti.FourTensor.weyl_kulkarniNomizu_innerₗ`,
  `TauCeti.FourTensor.weyl_eq_sub_kulkarniNomizu_schouten`, and
  `TauCeti.FourTensor.IsAlgebraicCurvature.weyl_eq_zero_of_finrank_le_three`: vanishing on
  Kulkarni–Nomizu products `h ⊙ g`, Schouten formula away from dimension `2`, and vanishing of the
  Weyl part in dimensions at most `3`.
* `TauCeti.FourTensor.sum_kulkarniNomizu_innerₗ_mul`,
  `TauCeti.FourTensor.IsAlgebraicCurvature.sum_sq_eq_add`,
  `TauCeti.FourTensor.IsAlgebraicCurvature.sum_sq_eq_scalar_add_tracelessRicci_add_weyl`:
  contraction adjointness, pairwise orthogonality, and the Pythagorean norm identity.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.G, Propositions 1.116–1.120.
* I. M. Singer and J. A. Thorpe, *The curvature of 4-dimensional Einstein spaces*, in *Global
  Analysis (Papers in Honor of K. Kodaira)*, Princeton Univ. Press (1969), 355–365.
-/

public section

open LinearMap (BilinForm)
open scoped RealInnerProductSpace

noncomputable section

namespace TauCeti

namespace FourTensor

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
private theorem isSymm_innerₗ (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] :
    LinearMap.BilinForm.IsSymm (innerₗ V) :=
  ⟨fun u v ↦ real_inner_comm v u⟩

private theorem eq_zero_of_finrank_eq_zero (hn : Module.finrank ℝ V = 0) (r : FourTensor V) :
    r = 0 := by
  have : Subsingleton V := Module.finrank_zero_iff.mp hn
  ext m
  exact r.map_coord_zero (0 : Fin 4) (Subsingleton.elim (m 0) 0)

private theorem bilinForm_eq_zero_of_finrank_eq_zero (hn : Module.finrank ℝ V = 0)
    (B : BilinForm ℝ V) : B = 0 := by
  have : Subsingleton V := Module.finrank_zero_iff.mp hn
  ext u v
  rw [Subsingleton.elim u 0]
  simp

private theorem kulkarniNomizu_innerₗ_self :
    kulkarniNomizu (innerₗ V) (innerₗ V) = (2 : ℝ) • constantCurvature V := by
  ext m
  have hm : m = ![m 0, m 1, m 2, m 3] := by funext i; fin_cases i <;> rfl
  rw [hm]
  simp only [kulkarniNomizu_apply, smul_apply, constantCurvature_apply, innerₗ_apply_apply,
    smul_eq_mul]
  ring

private theorem constantCurvature_eq_smul_kulkarniNomizu :
    constantCurvature V = (1 / 2 : ℝ) • kulkarniNomizu (innerₗ V) (innerₗ V) := by
  rw [kulkarniNomizu_innerₗ_self, smul_smul]
  norm_num

private theorem kulkarniNomizu_antisymm_first (h k : BilinForm ℝ V) (u v z w : V) :
    kulkarniNomizu h k ![u, v, z, w] = -kulkarniNomizu h k ![v, u, z, w] := by
  simp only [kulkarniNomizu_apply_eq]
  exact LinearMap.BilinForm.kulkarniNomizu_antisymm_first h k u v w z

private theorem kulkarniNomizu_antisymm_last (h k : BilinForm ℝ V) (u v z w : V) :
    kulkarniNomizu h k ![u, v, z, w] = -kulkarniNomizu h k ![u, v, w, z] := by
  simp only [kulkarniNomizu_apply_eq]
  exact LinearMap.BilinForm.kulkarniNomizu_antisymm_last h k u v w z

private theorem eq_zero_of_antisymm_first_of_finrank_le_one (hn : Module.finrank ℝ V ≤ 1)
    {q : FourTensor V} (hq₁ : ∀ u v z w, q ![u, v, z, w] = -q ![v, u, z, w]) : q = 0 := by
  apply toLinearMap₄_injective
  rw [map_zero]
  let b := (stdOrthonormalBasis ℝ V).toBasis
  refine b.ext fun i ↦ b.ext fun j ↦ b.ext fun k ↦ b.ext fun l ↦ ?_
  have hij : i = j := Fin.ext (by omega)
  rw [hij]
  simp only [toLinearMap₄_apply, LinearMap.zero_apply]
  linarith [hq₁ (b j) (b j) (b k) (b l)]

private theorem eq_smul_constantCurvature_of_antisymm_of_finrank_eq_two
    (hn : Module.finrank ℝ V = 2) {q : FourTensor V}
    (hq₁ : ∀ u v z w, q ![u, v, z, w] = -q ![v, u, z, w])
    (hq₂ : ∀ u v z w, q ![u, v, z, w] = -q ![u, v, w, z]) :
    q = q ![(stdOrthonormalBasis ℝ V).reindex (finCongr hn) 0,
      (stdOrthonormalBasis ℝ V).reindex (finCongr hn) 1,
      (stdOrthonormalBasis ℝ V).reindex (finCongr hn) 0,
      (stdOrthonormalBasis ℝ V).reindex (finCongr hn) 1] • constantCurvature V := by
  let b := (stdOrthonormalBasis ℝ V).reindex (finCongr hn)
  have hb0 : ⟪b 0, b 0⟫ = 1 := by simp
  have hb1 : ⟪b 1, b 1⟫ = 1 := by simp
  have hb01 : ⟪b 0, b 1⟫ = 0 := b.orthonormal.2 (by decide)
  have hb10 : ⟪b 1, b 0⟫ = 0 := b.orthonormal.2 (by decide)
  have hf0 : (⟨0, by decide⟩ : Fin 2) = 0 := rfl
  have hf1 : (⟨1, by decide⟩ : Fin 2) = 1 := rfl
  apply toLinearMap₄_injective
  refine b.toBasis.ext fun i ↦ b.toBasis.ext fun j ↦
    b.toBasis.ext fun k ↦ b.toBasis.ext fun l ↦ ?_
  simp only [OrthonormalBasis.coe_toBasis, map_smul, LinearMap.smul_apply,
    toLinearMap₄_apply, constantCurvature_apply, smul_eq_mul]
  by_cases hij : i = j
  · rw [hij]
    ring_nf
    linarith [hq₁ (b j) (b j) (b k) (b l)]
  by_cases hkl : k = l
  · rw [hkl]
    ring_nf
    linarith [hq₂ (b i) (b j) (b l) (b l)]
  fin_cases i <;> fin_cases j <;> try exact absurd rfl hij
  all_goals fin_cases k <;> fin_cases l <;> try exact absurd rfl hkl
  all_goals simp only [hf0, hf1, hb0, hb1, hb01, hb10]
  · ring
  · linarith [hq₂ (b 0) (b 1) (b 1) (b 0)]
  · linarith [hq₁ (b 1) (b 0) (b 0) (b 1)]
  · linarith [hq₁ (b 1) (b 0) (b 1) (b 0), hq₂ (b 0) (b 1) (b 1) (b 0)]

/-! ### The Ricci and trace-free Ricci endomorphisms -/

/-- The Ricci endomorphism on `V` associated with a four-tensor `r`, characterized by
`⟪ricciEnd r u, v⟫ = ricci r u v`. -/
def ricciEnd : FourTensor V →ₗ[ℝ] Module.End ℝ V where
  toFun r := (ricci r).symmCompOfNondegenerate (innerₗ V) TauCeti.nondegenerate_inner
  map_add' r q := LinearMap.ext fun u ↦ ext_inner_right ℝ fun v ↦ by
    rw [LinearMap.add_apply, inner_add_left]
    change innerₗ V _ v = innerₗ V _ v + innerₗ V _ v
    rw [LinearMap.BilinForm.symmCompOfNondegenerate_left_apply,
      LinearMap.BilinForm.symmCompOfNondegenerate_left_apply,
      LinearMap.BilinForm.symmCompOfNondegenerate_left_apply]
    simp
  map_smul' c r := LinearMap.ext fun u ↦ ext_inner_right ℝ fun v ↦ by
    rw [LinearMap.smul_apply, real_inner_smul_left, RingHom.id_apply]
    change innerₗ V _ v = c * innerₗ V _ v
    rw [LinearMap.BilinForm.symmCompOfNondegenerate_left_apply,
      LinearMap.BilinForm.symmCompOfNondegenerate_left_apply]
    simp

@[simp]
theorem inner_ricciEnd_left (r : FourTensor V) (u v : V) :
    ⟪ricciEnd r u, v⟫ = ricci r u v :=
  LinearMap.BilinForm.symmCompOfNondegenerate_left_apply (ricci r) TauCeti.nondegenerate_inner v u

theorem innerₗ_comp_ricciEnd (r : FourTensor V) :
    innerₗ V ∘ₗ ricciEnd r = ricci r := by
  ext u v
  exact inner_ricciEnd_left r u v

theorem IsAlgebraicCurvature.isSymmetric_ricciEnd {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) : (ricciEnd r).IsSymmetric := by
  intro u v
  rw [inner_ricciEnd_left, real_inner_comm, inner_ricciEnd_left]
  exact hr.isSymm_ricci.eq u v

theorem IsAlgebraicCurvature.inner_ricciEnd_right {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (u v : V) :
    ⟪u, ricciEnd r v⟫ = ricci r u v := by
  rw [← hr.isSymmetric_ricciEnd u v, inner_ricciEnd_left]

@[simp]
theorem trace_ricciEnd (r : FourTensor V) :
    LinearMap.trace ℝ V (ricciEnd r) = scalar r := by
  let b := stdOrthonormalBasis ℝ V
  rw [LinearMap.trace_eq_sum_inner _ b, scalar_apply, bilinFormTrace_eq_sum _ b]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [real_inner_comm, inner_ricciEnd_left]

@[simp]
theorem ricciEnd_constantCurvature :
    ricciEnd (constantCurvature V) = ((Module.finrank ℝ V : ℝ) - 1) • LinearMap.id := by
  ext u
  refine ext_inner_right ℝ fun v ↦ ?_
  simp [ricci_constantCurvature, real_inner_smul_left]

/-- The trace-free Ricci bilinear form `Ric₀(r) = Ric(r) - (Scal(r) / n) g`. -/
def tracelessRicci : FourTensor V →ₗ[ℝ] BilinForm ℝ V where
  toFun r := ricci r - (scalar r / Module.finrank ℝ V) • innerₗ V
  map_add' r q := by
    ext u v
    simp only [map_add, add_div, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
      innerₗ_apply_apply, smul_eq_mul]
    ring
  map_smul' c r := by
    ext u v
    simp only [map_smul, RingHom.id_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      innerₗ_apply_apply, smul_eq_mul, mul_div_assoc]
    ring

theorem tracelessRicci_apply (r : FourTensor V) :
    tracelessRicci r = ricci r - (scalar r / Module.finrank ℝ V) • innerₗ V :=
  (rfl)

@[simp]
theorem tracelessRicci_apply_apply (r : FourTensor V) (u v : V) :
    tracelessRicci r u v = ricci r u v - scalar r / Module.finrank ℝ V * ⟪u, v⟫ := by
  simp [tracelessRicci_apply]

@[simp]
theorem bilinFormTrace_tracelessRicci (r : FourTensor V) :
    bilinFormTrace (tracelessRicci r) = 0 := by
  rcases eq_or_ne (Module.finrank ℝ V) 0 with hn | hn
  · rw [bilinForm_eq_zero_of_finrank_eq_zero hn (tracelessRicci r), map_zero]
  · have hn' : (Module.finrank ℝ V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    let b := stdOrthonormalBasis ℝ V
    have h1 : ∑ i, ⟪b i, b i⟫ = (Module.finrank ℝ V : ℝ) := by simp
    rw [bilinFormTrace_eq_sum _ b]
    simp only [tracelessRicci_apply_apply, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← bilinFormTrace_eq_sum (ricci r) b, ← scalar_apply, h1, div_mul_cancel₀ _ hn', sub_self]

theorem IsAlgebraicCurvature.isSymm_tracelessRicci {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) : (tracelessRicci r).IsSymm :=
  ⟨fun u v ↦ by simp [hr.isSymm_ricci.eq u v, real_inner_comm u v]⟩

@[simp]
theorem tracelessRicci_constantCurvature :
    tracelessRicci (constantCurvature V) = 0 := by
  rcases eq_or_ne (Module.finrank ℝ V) 0 with hn | hn
  · exact bilinForm_eq_zero_of_finrank_eq_zero hn _
  · have hn' : (Module.finrank ℝ V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    ext u v
    rw [tracelessRicci_apply_apply, ricci_constantCurvature, scalar_constantCurvature]
    simp only [LinearMap.smul_apply, innerₗ_apply_apply, smul_eq_mul, LinearMap.zero_apply]
    rw [mul_div_cancel_left₀ _ hn', sub_self]

/-- The trace-free Ricci endomorphism `ricciEnd r - (scalar r / n) • Id` on `V`. -/
def tracelessRicciEnd : FourTensor V →ₗ[ℝ] Module.End ℝ V :=
  ricciEnd (V := V) - ((Module.finrank ℝ V : ℝ)⁻¹ • scalar (V := V)).smulRight LinearMap.id

theorem tracelessRicciEnd_apply (r : FourTensor V) :
    tracelessRicciEnd r = ricciEnd r - (scalar r / Module.finrank ℝ V) • LinearMap.id := by
  ext u
  simp [tracelessRicciEnd, div_eq_inv_mul]

@[simp]
theorem inner_tracelessRicciEnd_left (r : FourTensor V) (u v : V) :
    ⟪tracelessRicciEnd r u, v⟫ = tracelessRicci r u v := by
  simp [tracelessRicciEnd_apply, inner_sub_left, real_inner_smul_left]

theorem innerₗ_comp_tracelessRicciEnd (r : FourTensor V) :
    innerₗ V ∘ₗ tracelessRicciEnd r = tracelessRicci r := by
  ext u v
  exact inner_tracelessRicciEnd_left r u v

theorem IsAlgebraicCurvature.isSymmetric_tracelessRicciEnd {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) : (tracelessRicciEnd r).IsSymmetric := by
  intro u v
  rw [inner_tracelessRicciEnd_left, real_inner_comm, inner_tracelessRicciEnd_left]
  exact hr.isSymm_tracelessRicci.eq u v

@[simp]
theorem trace_tracelessRicciEnd (r : FourTensor V) :
    LinearMap.trace ℝ V (tracelessRicciEnd r) = 0 := by
  let b := stdOrthonormalBasis ℝ V
  rw [LinearMap.trace_eq_sum_inner _ b, ← bilinFormTrace_tracelessRicci r,
    bilinFormTrace_eq_sum _ b]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [real_inner_comm, inner_tracelessRicciEnd_left]

@[simp]
theorem tracelessRicciEnd_constantCurvature :
    tracelessRicciEnd (constantCurvature V) = 0 := by
  ext u
  refine ext_inner_right ℝ fun v ↦ ?_
  simp

/-! ### The scalar, trace-free Ricci, Schouten, and Weyl components -/

/-- The scalar curvature component `(scalar r / (n (n - 1))) • constantCurvature V` of a
four-tensor. -/
def scalarPart : FourTensor V →ₗ[ℝ] FourTensor V :=
  (((Module.finrank ℝ V : ℝ) * ((Module.finrank ℝ V : ℝ) - 1))⁻¹ • scalar (V := V)).smulRight
    (constantCurvature V)

theorem scalarPart_apply (r : FourTensor V) :
    scalarPart r =
      (scalar r / ((Module.finrank ℝ V : ℝ) * ((Module.finrank ℝ V : ℝ) - 1))) •
        constantCurvature V := by
  ext m
  simp [scalarPart, div_eq_inv_mul]

theorem isAlgebraicCurvature_scalarPart (r : FourTensor V) :
    IsAlgebraicCurvature (scalarPart r) := by
  rw [scalarPart_apply]
  exact mem_algebraicCurvatureSubmodule.mp <|
    (algebraicCurvatureSubmodule V).smul_mem _
      (mem_algebraicCurvatureSubmodule.mpr isAlgebraicCurvature_constantCurvature)

/-- The trace-free Ricci component `(n - 2)⁻¹ • kulkarniNomizu (tracelessRicci r) (innerₗ V)` of a
four-tensor. -/
def tracelessRicciPart : FourTensor V →ₗ[ℝ] FourTensor V :=
  ((Module.finrank ℝ V : ℝ) - 2)⁻¹ • (kulkarniNomizu.flip (innerₗ V) ∘ₗ tracelessRicci (V := V))

theorem tracelessRicciPart_apply (r : FourTensor V) :
    tracelessRicciPart r =
      ((Module.finrank ℝ V : ℝ) - 2)⁻¹ • kulkarniNomizu (tracelessRicci r) (innerₗ V) :=
  (rfl)

theorem IsAlgebraicCurvature.tracelessRicciPart {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) : IsAlgebraicCurvature (FourTensor.tracelessRicciPart r) := by
  rw [tracelessRicciPart_apply]
  exact mem_algebraicCurvatureSubmodule.mp <|
    (algebraicCurvatureSubmodule V).smul_mem _
      (mem_algebraicCurvatureSubmodule.mpr
        (isAlgebraicCurvature_kulkarniNomizu hr.isSymm_tracelessRicci (isSymm_innerₗ V)))

/-- The Schouten bilinear form `P(r) = (n - 2)⁻¹ • (Ric(r) - (Scal(r) / (2 (n - 1))) g)`. -/
def schouten : FourTensor V →ₗ[ℝ] BilinForm ℝ V where
  toFun r :=
    ((Module.finrank ℝ V : ℝ) - 2)⁻¹ •
      (ricci r - (scalar r / (2 * ((Module.finrank ℝ V : ℝ) - 1))) • innerₗ V)
  map_add' r q := by
    ext u v
    simp only [map_add, add_div, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.add_apply,
      innerₗ_apply_apply, smul_eq_mul]
    ring
  map_smul' c r := by
    ext u v
    simp only [map_smul, RingHom.id_apply, LinearMap.smul_apply, LinearMap.sub_apply,
      innerₗ_apply_apply, smul_eq_mul, mul_div_assoc]
    ring

theorem schouten_apply (r : FourTensor V) :
    schouten r =
      ((Module.finrank ℝ V : ℝ) - 2)⁻¹ •
        (ricci r - (scalar r / (2 * ((Module.finrank ℝ V : ℝ) - 1))) • innerₗ V) :=
  (rfl)

theorem IsAlgebraicCurvature.isSymm_schouten {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    (schouten r).IsSymm := by
  refine ⟨fun u v ↦ ?_⟩
  simp only [schouten_apply, LinearMap.smul_apply, LinearMap.sub_apply, innerₗ_apply_apply,
    smul_eq_mul, hr.isSymm_ricci.eq u v, real_inner_comm u v]

/-- The Weyl component `r - scalarPart r - tracelessRicciPart r` of a four-tensor. -/
def weyl : FourTensor V →ₗ[ℝ] FourTensor V :=
  LinearMap.id - scalarPart - tracelessRicciPart

theorem weyl_apply (r : FourTensor V) :
    weyl r = r - scalarPart r - tracelessRicciPart r :=
  (rfl)

/-- **Ricci–Weyl decomposition**: every four-tensor is the sum of its scalar, trace-free Ricci, and
Weyl parts. -/
theorem scalarPart_add_tracelessRicciPart_add_weyl (r : FourTensor V) :
    scalarPart r + tracelessRicciPart r + weyl r = r := by
  rw [weyl_apply]
  abel

theorem IsAlgebraicCurvature.weyl {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    IsAlgebraicCurvature (FourTensor.weyl r) := by
  rw [weyl_apply]
  exact mem_algebraicCurvatureSubmodule.mp <|
    (algebraicCurvatureSubmodule V).sub_mem
      ((algebraicCurvatureSubmodule V).sub_mem (mem_algebraicCurvatureSubmodule.mpr hr)
        (mem_algebraicCurvatureSubmodule.mpr (isAlgebraicCurvature_scalarPart r)))
      (mem_algebraicCurvatureSubmodule.mpr hr.tracelessRicciPart)

/-! ### Bivector curvature operators of the decomposition pieces -/

/-- The scalar curvature component acts on `⋀[ℝ]^2 V` as `(scalar r / (n (n - 1))) • Id`. -/
@[simp]
theorem curvatureOperator_scalarPart (r : FourTensor V) :
    curvatureOperator ⟨scalarPart r, mem_algebraicCurvatureSubmodule.mpr
      (isAlgebraicCurvature_scalarPart r)⟩ =
      (scalar r / ((Module.finrank ℝ V : ℝ) * ((Module.finrank ℝ V : ℝ) - 1))) •
        LinearMap.id := by
  have hsub :
      (⟨scalarPart r, mem_algebraicCurvatureSubmodule.mpr (isAlgebraicCurvature_scalarPart r)⟩ :
          algebraicCurvatureSubmodule V) =
        (scalar r / ((Module.finrank ℝ V : ℝ) * ((Module.finrank ℝ V : ℝ) - 1))) •
          ⟨constantCurvature V,
            mem_algebraicCurvatureSubmodule.mpr isAlgebraicCurvature_constantCurvature⟩ :=
    Subtype.ext (scalarPart_apply r)
  rw [hsub, map_smul, curvatureOperator_constantCurvature]

/-- The trace-free Ricci component of an algebraic curvature tensor acts on `⋀[ℝ]^2 V` as
`(2 / (n - 2)) • wedgeEnd (tracelessRicciEnd r) Id`. -/
theorem IsAlgebraicCurvature.curvatureOperator_tracelessRicciPart {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) :
    curvatureOperator ⟨FourTensor.tracelessRicciPart r,
        mem_algebraicCurvatureSubmodule.mpr hr.tracelessRicciPart⟩ =
      (2 / ((Module.finrank ℝ V : ℝ) - 2)) • wedgeEnd (tracelessRicciEnd r) LinearMap.id := by
  rw [curvatureOperator_eq_iff]
  intro u v z w
  have hid : innerₗ V ∘ₗ (LinearMap.id : Module.End ℝ V) = innerₗ V := rfl
  dsimp only
  rw [LinearMap.smul_apply, real_inner_smul_left, inner_wedgeEnd_ιMulti,
    innerₗ_comp_tracelessRicciEnd, hid, tracelessRicciPart_apply, smul_apply, smul_eq_mul]
  ring

/-- **Bivector operator decomposition**: the curvature operator of `r` splits into its scalar
multiple of the identity, its symmetric wedge `(2 / (n - 2)) • (Ric₀ ∧ Id)`, and the Weyl operator
in every dimension. -/
theorem IsAlgebraicCurvature.curvatureOperator_eq {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) :
    curvatureOperator ⟨r, mem_algebraicCurvatureSubmodule.mpr hr⟩ =
      (scalar r / ((Module.finrank ℝ V : ℝ) * ((Module.finrank ℝ V : ℝ) - 1))) • LinearMap.id +
        (2 / ((Module.finrank ℝ V : ℝ) - 2)) • wedgeEnd (tracelessRicciEnd r) LinearMap.id +
        curvatureOperator ⟨FourTensor.weyl r, mem_algebraicCurvatureSubmodule.mpr hr.weyl⟩ := by
  have hsum :
      (⟨r, mem_algebraicCurvatureSubmodule.mpr hr⟩ : algebraicCurvatureSubmodule V) =
        ⟨scalarPart r, mem_algebraicCurvatureSubmodule.mpr (isAlgebraicCurvature_scalarPart r)⟩ +
          ⟨FourTensor.tracelessRicciPart r,
            mem_algebraicCurvatureSubmodule.mpr hr.tracelessRicciPart⟩ +
          ⟨FourTensor.weyl r, mem_algebraicCurvatureSubmodule.mpr hr.weyl⟩ :=
    Subtype.ext (scalarPart_add_tracelessRicciPart_add_weyl r).symm
  rw [hsum, map_add, map_add, curvatureOperator_scalarPart, hr.curvatureOperator_tracelessRicciPart]

/-! ### Contractions, idempotence, and mutual annihilation -/

@[simp]
theorem scalarPart_constantCurvature :
    scalarPart (constantCurvature V) = constantCurvature V := by
  rcases le_or_gt (Module.finrank ℝ V) 1 with hn | hn
  · have hc : constantCurvature V = 0 :=
      isAlgebraicCurvature_constantCurvature.eq_zero_of_finrank_le_one hn
    simp [hc]
  · have hn0 : (Module.finrank ℝ V : ℝ) ≠ 0 := by positivity
    have hn1 : (Module.finrank ℝ V : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ Module.finrank ℝ V := by exact_mod_cast hn
      linarith
    rw [scalarPart_apply, scalar_constantCurvature, div_self (mul_ne_zero hn0 hn1), one_smul]

@[simp]
theorem scalarPart_scalarPart (r : FourTensor V) :
    scalarPart (scalarPart r) = scalarPart r := by
  rw [scalarPart_apply r, map_smul, scalarPart_constantCurvature]

@[simp]
theorem tracelessRicci_scalarPart (r : FourTensor V) :
    tracelessRicci (scalarPart r) = 0 := by
  rw [scalarPart_apply, map_smul, tracelessRicci_constantCurvature, smul_zero]

@[simp]
theorem tracelessRicciPart_constantCurvature :
    tracelessRicciPart (constantCurvature V) = 0 := by
  simp [tracelessRicciPart_apply]

@[simp]
theorem tracelessRicciPart_scalarPart (r : FourTensor V) :
    tracelessRicciPart (scalarPart r) = 0 := by
  simp [tracelessRicciPart_apply]

theorem IsAlgebraicCurvature.ricci_scalarPart {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    ricci (scalarPart r) = (scalar r / Module.finrank ℝ V) • innerₗ V := by
  rcases le_or_gt (Module.finrank ℝ V) 1 with hn | hn
  · rw [hr.eq_zero_of_finrank_le_one hn]
    simp
  · have hn1 : (Module.finrank ℝ V : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ Module.finrank ℝ V := by exact_mod_cast hn
      linarith
    rw [scalarPart_apply, map_smul, ricci_constantCurvature, smul_smul]
    congr 1
    field_simp

theorem IsAlgebraicCurvature.scalar_scalarPart {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    scalar (scalarPart r) = scalar r := by
  rcases eq_or_ne (Module.finrank ℝ V) 0 with hn | hn
  · rw [eq_zero_of_finrank_eq_zero hn r, map_zero, map_zero]
  · have hn' : (Module.finrank ℝ V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [scalar_apply, hr.ricci_scalarPart, map_smul, bilinFormTrace_inner, smul_eq_mul,
      div_mul_cancel₀ _ hn']

@[simp]
theorem scalar_tracelessRicciPart (r : FourTensor V) :
    scalar (tracelessRicciPart r) = 0 := by
  rw [tracelessRicciPart_apply, map_smul, scalar_kulkarniNomizu_innerₗ,
    bilinFormTrace_tracelessRicci, mul_zero, smul_zero]

@[simp]
theorem scalarPart_tracelessRicciPart (r : FourTensor V) :
    scalarPart (tracelessRicciPart r) = 0 := by
  rw [scalarPart_apply, scalar_tracelessRicciPart, zero_div, zero_smul]

/-- Away from dimension `2`, `ricci (tracelessRicciPart r) = tracelessRicci r` for every
four-tensor `r`. -/
theorem ricci_tracelessRicciPart_of_ne_two (hn : Module.finrank ℝ V ≠ 2) (r : FourTensor V) :
    ricci (tracelessRicciPart r) = tracelessRicci r := by
  have hn2' : (Module.finrank ℝ V : ℝ) - 2 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hn)
  rw [tracelessRicciPart_apply, map_smul, ricci_kulkarniNomizu_innerₗ,
    bilinFormTrace_tracelessRicci, zero_smul, add_zero, smul_smul, inv_mul_cancel₀ hn2', one_smul]

theorem IsAlgebraicCurvature.ricci_tracelessRicciPart {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) :
    ricci (FourTensor.tracelessRicciPart r) = tracelessRicci r := by
  rcases eq_or_ne (Module.finrank ℝ V) 2 with hn2 | hn2
  · have hr2 := hr.eq_smul_constantCurvature_of_finrank_eq_two hn2
    have htr : tracelessRicci r = 0 := by
      rw [hr2, map_smul, tracelessRicci_constantCurvature, smul_zero]
    rw [tracelessRicciPart_apply, hn2]
    norm_num [htr]
  · exact ricci_tracelessRicciPart_of_ne_two hn2 r

theorem IsAlgebraicCurvature.tracelessRicci_tracelessRicciPart {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) :
    tracelessRicci (FourTensor.tracelessRicciPart r) = tracelessRicci r := by
  ext u v
  simp [hr.ricci_tracelessRicciPart]

@[simp]
theorem tracelessRicciPart_tracelessRicciPart (r : FourTensor V) :
    tracelessRicciPart (tracelessRicciPart r) = tracelessRicciPart r := by
  rcases eq_or_ne (Module.finrank ℝ V) 2 with hn2 | hn2
  · simp [tracelessRicciPart_apply, hn2]
  · have hric : tracelessRicci (tracelessRicciPart r) = tracelessRicci r := by
      ext u v
      simp [ricci_tracelessRicciPart_of_ne_two hn2 r]
    rw [tracelessRicciPart_apply (tracelessRicciPart r), hric, ← tracelessRicciPart_apply]

/-- **The Weyl part of every algebraic curvature tensor is Ricci-flat in all dimensions.** -/
theorem IsAlgebraicCurvature.ricci_weyl {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    ricci (FourTensor.weyl r) = 0 := by
  rw [weyl_apply, map_sub, map_sub, hr.ricci_scalarPart, hr.ricci_tracelessRicciPart,
    tracelessRicci_apply]
  abel

/-- **The Weyl part of every algebraic curvature tensor has zero scalar contraction.** -/
theorem IsAlgebraicCurvature.scalar_weyl {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    scalar (FourTensor.weyl r) = 0 := by
  rw [scalar_apply, hr.ricci_weyl, map_zero]

theorem IsAlgebraicCurvature.tracelessRicci_weyl {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) : tracelessRicci (FourTensor.weyl r) = 0 := by
  ext u v
  simp [hr.ricci_weyl, hr.scalar_weyl]

@[simp]
theorem scalarPart_weyl (r : FourTensor V) : scalarPart (weyl r) = 0 := by
  rcases le_or_gt (Module.finrank ℝ V) 1 with hn | hn
  · have hc : constantCurvature V = 0 :=
      isAlgebraicCurvature_constantCurvature.eq_zero_of_finrank_le_one hn
    simp [scalarPart_apply, hc]
  · have hn0 : (Module.finrank ℝ V : ℝ) ≠ 0 := by positivity
    have hn1 : (Module.finrank ℝ V : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ Module.finrank ℝ V := by exact_mod_cast hn
      linarith
    have hscal : scalar (scalarPart r) = scalar r := by
      rw [scalarPart_apply, map_smul, scalar_constantCurvature, smul_eq_mul,
        div_mul_cancel₀ _ (mul_ne_zero hn0 hn1)]
    rw [scalarPart_apply, weyl_apply, map_sub, map_sub, hscal, scalar_tracelessRicciPart,
      sub_self, sub_zero, zero_div, zero_smul]

@[simp]
theorem tracelessRicciPart_weyl (r : FourTensor V) : tracelessRicciPart (weyl r) = 0 := by
  rcases eq_or_ne (Module.finrank ℝ V) 2 with hn2 | hn2
  · simp [tracelessRicciPart_apply, hn2]
  · have htr : tracelessRicci (tracelessRicciPart r) = tracelessRicci r := by
      ext u v
      simp [ricci_tracelessRicciPart_of_ne_two hn2 r]
    have htr_weyl : tracelessRicci (weyl r) = 0 := by
      rw [weyl_apply, map_sub, map_sub, tracelessRicci_scalarPart, htr]
      abel
    rw [tracelessRicciPart_apply, htr_weyl, map_zero, LinearMap.zero_apply, smul_zero]

/-- **Idempotence of the Weyl projection.** -/
@[simp]
theorem weyl_weyl (r : FourTensor V) : weyl (weyl r) = weyl r := by
  rw [weyl_apply (weyl r), scalarPart_weyl, tracelessRicciPart_weyl, sub_zero, sub_zero]

@[simp]
theorem weyl_constantCurvature : weyl (constantCurvature V) = 0 := by
  rw [weyl_apply, scalarPart_constantCurvature, tracelessRicciPart_constantCurvature, sub_self,
    sub_zero]

@[simp]
theorem weyl_scalarPart (r : FourTensor V) : weyl (scalarPart r) = 0 := by
  rw [scalarPart_apply, map_smul, weyl_constantCurvature, smul_zero]

@[simp]
theorem weyl_tracelessRicciPart (r : FourTensor V) : weyl (tracelessRicciPart r) = 0 := by
  rw [weyl_apply, scalarPart_tracelessRicciPart, tracelessRicciPart_tracelessRicciPart, sub_zero,
    sub_self]

/-! ### Comparison with the Schouten tensor and vanishing on `h ⊙ g` -/

/-- In dimension at least `3`, the Schouten bilinear form splits as
`(n - 2)⁻¹ • tracelessRicci r + (scalar r / (2 n (n - 1))) • innerₗ V`. -/
theorem schouten_eq_add_of_three_le (hn : 3 ≤ Module.finrank ℝ V) (r : FourTensor V) :
    schouten r =
      ((Module.finrank ℝ V : ℝ) - 2)⁻¹ • tracelessRicci r +
        (scalar r / (2 * (Module.finrank ℝ V : ℝ) * ((Module.finrank ℝ V : ℝ) - 1))) •
          innerₗ V := by
  have hn3 : (3 : ℝ) ≤ Module.finrank ℝ V := by exact_mod_cast hn
  have hn0 : (Module.finrank ℝ V : ℝ) ≠ 0 := by linarith
  have hn1 : (Module.finrank ℝ V : ℝ) - 1 ≠ 0 := by linarith
  have hn2 : (Module.finrank ℝ V : ℝ) - 2 ≠ 0 := by linarith
  ext u v
  simp only [schouten_apply, tracelessRicci_apply, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, innerₗ_apply_apply, smul_eq_mul]
  field_simp
  ring

/-- Away from dimension `2`, the Kulkarni–Nomizu product of the Schouten tensor of any four-tensor
with the inner product equals `scalarPart r + tracelessRicciPart r`. -/
theorem kulkarniNomizu_schouten_innerₗ (hn : Module.finrank ℝ V ≠ 2) (r : FourTensor V) :
    kulkarniNomizu (schouten r) (innerₗ V) = scalarPart r + tracelessRicciPart r := by
  rcases lt_or_gt_of_ne hn with hnlt | hngt
  · have hle : Module.finrank ℝ V ≤ 1 := by omega
    have hkn (h k : BilinForm ℝ V) : kulkarniNomizu h k = 0 :=
      eq_zero_of_antisymm_first_of_finrank_le_one hle (kulkarniNomizu_antisymm_first h k)
    rw [hkn, scalarPart_apply, constantCurvature_eq_smul_kulkarniNomizu, hkn,
      tracelessRicciPart_apply, hkn]
    simp
  · have hn3 : (3 : ℝ) ≤ Module.finrank ℝ V := by exact_mod_cast hngt
    have hn0 : (Module.finrank ℝ V : ℝ) ≠ 0 := by linarith
    have hn1 : (Module.finrank ℝ V : ℝ) - 1 ≠ 0 := by linarith
    rw [schouten_eq_add_of_three_le hngt r, map_add, LinearMap.add_apply, map_smul, map_smul,
      LinearMap.smul_apply, LinearMap.smul_apply, ← tracelessRicciPart_apply, scalarPart_apply,
      constantCurvature_eq_smul_kulkarniNomizu, smul_smul, add_comm]
    congr 2
    field_simp

/-- Away from dimension `2`, the Weyl part of any four-tensor is
`r - kulkarniNomizu (schouten r) (innerₗ V)`. -/
theorem weyl_eq_sub_kulkarniNomizu_schouten (hn : Module.finrank ℝ V ≠ 2) (r : FourTensor V) :
    weyl r = r - kulkarniNomizu (schouten r) (innerₗ V) := by
  rw [kulkarniNomizu_schouten_innerₗ hn r, weyl_apply, sub_sub]

/-- Away from dimension `2`, the metric trace of `schouten r` for an algebraic curvature tensor is
`scalar r / (2 (n - 1))`. -/
theorem IsAlgebraicCurvature.bilinFormTrace_schouten {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (hn : Module.finrank ℝ V ≠ 2) :
    bilinFormTrace (schouten r) = scalar r / (2 * ((Module.finrank ℝ V : ℝ) - 1)) := by
  rcases lt_or_gt_of_ne hn with hnlt | hngt
  · have hle : Module.finrank ℝ V ≤ 1 := by omega
    rw [hr.eq_zero_of_finrank_le_one hle]
    simp
  · have hn3 : (3 : ℝ) ≤ Module.finrank ℝ V := by exact_mod_cast hngt
    have hn0 : (Module.finrank ℝ V : ℝ) ≠ 0 := by linarith
    have hn1 : (Module.finrank ℝ V : ℝ) - 1 ≠ 0 := by linarith
    rw [schouten_eq_add_of_three_le hngt r, map_add, map_smul, bilinFormTrace_tracelessRicci,
      smul_zero, zero_add, map_smul, bilinFormTrace_inner, smul_eq_mul]
    field_simp

/-- In every dimension, `weyl (kulkarniNomizu h (innerₗ V)) = 0` for every bilinear form `h`. -/
@[simp]
theorem weyl_kulkarniNomizu_innerₗ (h : BilinForm ℝ V) :
    weyl (kulkarniNomizu h (innerₗ V)) = 0 := by
  have hcases : Module.finrank ℝ V ≤ 1 ∨ Module.finrank ℝ V = 2 ∨ 3 ≤ Module.finrank ℝ V := by
    omega
  rcases hcases with h1 | h2 | h3
  · rw [eq_zero_of_antisymm_first_of_finrank_le_one h1
      (kulkarniNomizu_antisymm_first h (innerₗ V)), map_zero]
  · rw [eq_smul_constantCurvature_of_antisymm_of_finrank_eq_two h2
      (kulkarniNomizu_antisymm_first h (innerₗ V))
      (kulkarniNomizu_antisymm_last h (innerₗ V)), map_smul, weyl_constantCurvature, smul_zero]
  · have hn3 : (3 : ℝ) ≤ Module.finrank ℝ V := by exact_mod_cast h3
    have hn0 : (Module.finrank ℝ V : ℝ) ≠ 0 := by linarith
    have hn1 : (Module.finrank ℝ V : ℝ) - 1 ≠ 0 := by linarith
    have hn2 : (Module.finrank ℝ V : ℝ) - 2 ≠ 0 := by linarith
    have hsc : scalarPart (kulkarniNomizu h (innerₗ V)) =
        (bilinFormTrace h / Module.finrank ℝ V) • kulkarniNomizu (innerₗ V) (innerₗ V) := by
      rw [scalarPart_apply, scalar_kulkarniNomizu_innerₗ,
        constantCurvature_eq_smul_kulkarniNomizu, smul_smul]
      congr 1
      field_simp
    have htr : tracelessRicci (kulkarniNomizu h (innerₗ V)) =
        ((Module.finrank ℝ V : ℝ) - 2) •
          (h - (bilinFormTrace h / Module.finrank ℝ V) • innerₗ V) := by
      ext u v
      rw [tracelessRicci_apply_apply, ricci_kulkarniNomizu_innerₗ, scalar_kulkarniNomizu_innerₗ]
      simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        innerₗ_apply_apply, smul_eq_mul]
      field_simp
      ring
    have htrp : tracelessRicciPart (kulkarniNomizu h (innerₗ V)) =
        kulkarniNomizu h (innerₗ V) -
          (bilinFormTrace h / Module.finrank ℝ V) • kulkarniNomizu (innerₗ V) (innerₗ V) := by
      ext m
      have hm : m = ![m 0, m 1, m 2, m 3] := by funext i; fin_cases i <;> rfl
      rw [hm, tracelessRicciPart_apply, htr, sub_apply, smul_apply, smul_apply,
        kulkarniNomizu_apply, kulkarniNomizu_apply, kulkarniNomizu_apply]
      simp only [LinearMap.smul_apply, LinearMap.sub_apply, innerₗ_apply_apply, smul_eq_mul]
      field_simp
      ring
    rw [weyl_apply, hsc, htrp]
    abel

/-! ### Vanishing of the Weyl tensor in dimension at most three -/

/-- **In dimension `3`, the Weyl part of every algebraic curvature tensor vanishes.** -/
theorem IsAlgebraicCurvature.weyl_eq_zero_of_finrank_eq_three {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (hn : Module.finrank ℝ V = 3) :
    FourTensor.weyl r = 0 := by
  apply toLinearMap₄_injective
  rw [map_zero]
  let b := stdOrthonormalBasis ℝ V
  have hcard : Fintype.card (Fin (Module.finrank ℝ V)) = 3 := by simp [hn]
  have h2 : IsSMulRegular ℝ (2 : ℝ) := fun x y hxy ↦ by
    simp only [smul_eq_mul] at hxy
    linarith
  have hw := hr.weyl
  refine LinearMap.eq_zero_of_sum_basis_eq_zero_of_card_eq_three h2 b.toBasis hcard
    (fun x y z w ↦ by simp [hw.antisymm_first x y z w])
    (fun x y z w ↦ by simp [hw.antisymm_last x y z w])
    fun y z ↦ ?_
  have hsum : ∑ i, (FourTensor.weyl r).toLinearMap₄ (b i) y z (b i) =
      -ricci (FourTensor.weyl r) y z := by
    rw [ricci_apply_orthonormalBasis b, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simpa [toLinearMap₄_apply] using hw.antisymm_last (b i) y z (b i)
  simp only [OrthonormalBasis.coe_toBasis]
  rw [hsum, hr.ricci_weyl]
  simp

/-- **In dimension at most `3`, the Weyl part of every algebraic curvature tensor vanishes.** -/
theorem IsAlgebraicCurvature.weyl_eq_zero_of_finrank_le_three {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (hn : Module.finrank ℝ V ≤ 3) :
    FourTensor.weyl r = 0 := by
  have hcases : Module.finrank ℝ V ≤ 1 ∨ Module.finrank ℝ V = 2 ∨ Module.finrank ℝ V = 3 := by
    omega
  rcases hcases with h1 | h2 | h3
  · rw [hr.eq_zero_of_finrank_le_one h1, map_zero]
  · rw [hr.eq_smul_constantCurvature_of_finrank_eq_two h2, map_smul, weyl_constantCurvature,
      smul_zero]
  · exact hr.weyl_eq_zero_of_finrank_eq_three h3

/-- In dimension at most `3`, every algebraic curvature tensor is recovered from its scalar and
trace-free Ricci parts: `r = scalarPart r + tracelessRicciPart r`. -/
theorem IsAlgebraicCurvature.eq_scalarPart_add_tracelessRicciPart_of_finrank_le_three
    {r : FourTensor V} (hr : IsAlgebraicCurvature r) (hn : Module.finrank ℝ V ≤ 3) :
    r = scalarPart r + FourTensor.tracelessRicciPart r := by
  have h := scalarPart_add_tracelessRicciPart_add_weyl r
  rw [hr.weyl_eq_zero_of_finrank_le_three hn, add_zero] at h
  exact h.symm

/-! ### Equivariance under linear isometric equivalences -/

section Equivariance

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

theorem tracelessRicci_compContinuousLinearMap_linearIsometryEquiv (e : W ≃ₗᵢ[ℝ] V)
    (r : FourTensor V) (u v : W) :
    tracelessRicci (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap)
        u v = tracelessRicci r (e u) (e v) := by
  rw [tracelessRicci_apply_apply, tracelessRicci_apply_apply,
    ricci_compContinuousLinearMap_linearIsometryEquiv,
    scalar_compContinuousLinearMap_linearIsometryEquiv, e.toLinearEquiv.finrank_eq,
    e.inner_map_map]

theorem ricciEnd_compContinuousLinearMap_linearIsometryEquiv (e : W ≃ₗᵢ[ℝ] V)
    (r : FourTensor V) :
    ricciEnd (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      e.toLinearEquiv.symm.conj (ricciEnd r) := by
  ext u
  refine ext_inner_right ℝ fun v ↦ ?_
  have hcancel :
      e ((LinearEquiv.symm e.toLinearEquiv) (ricciEnd r (e.toLinearEquiv u))) =
        ricciEnd r (e u) :=
    e.toLinearEquiv.apply_symm_apply _
  rw [inner_ricciEnd_left, ricci_compContinuousLinearMap_linearIsometryEquiv]
  simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_symm]
  rw [← e.inner_map_map, hcancel, inner_ricciEnd_left]

theorem tracelessRicciEnd_compContinuousLinearMap_linearIsometryEquiv (e : W ≃ₗᵢ[ℝ] V)
    (r : FourTensor V) :
    tracelessRicciEnd
        (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      e.toLinearEquiv.symm.conj (tracelessRicciEnd r) := by
  rw [tracelessRicciEnd_apply, tracelessRicciEnd_apply, map_sub, map_smul, LinearEquiv.conj_id,
    ricciEnd_compContinuousLinearMap_linearIsometryEquiv,
    scalar_compContinuousLinearMap_linearIsometryEquiv, e.toLinearEquiv.finrank_eq]

theorem scalarPart_compContinuousLinearMap_linearIsometryEquiv (e : W ≃ₗᵢ[ℝ] V)
    (r : FourTensor V) :
    scalarPart (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      (scalarPart r).compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap := by
  ext m
  have hm : m = ![m 0, m 1, m 2, m 3] := by funext i; fin_cases i <;> rfl
  rw [hm, compContinuousLinearMap_apply_vec, scalarPart_apply, scalarPart_apply, smul_apply,
    smul_apply, scalar_compContinuousLinearMap_linearIsometryEquiv, e.toLinearEquiv.finrank_eq]
  congr 1
  simp only [constantCurvature_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, e.inner_map_map]

theorem tracelessRicciPart_compContinuousLinearMap_linearIsometryEquiv (e : W ≃ₗᵢ[ℝ] V)
    (r : FourTensor V) :
    tracelessRicciPart
        (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      (tracelessRicciPart r).compContinuousLinearMap fun _ ↦
        e.toLinearIsometry.toContinuousLinearMap := by
  ext m
  have hm : m = ![m 0, m 1, m 2, m 3] := by funext i; fin_cases i <;> rfl
  rw [hm, compContinuousLinearMap_apply_vec, tracelessRicciPart_apply, tracelessRicciPart_apply,
    smul_apply, smul_apply, e.toLinearEquiv.finrank_eq]
  congr 1
  simp only [kulkarniNomizu_apply, innerₗ_apply_apply,
    tracelessRicci_compContinuousLinearMap_linearIsometryEquiv,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    e.inner_map_map]

theorem schouten_compContinuousLinearMap_linearIsometryEquiv (e : W ≃ₗᵢ[ℝ] V)
    (r : FourTensor V) (u v : W) :
    schouten (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) u v =
      schouten r (e u) (e v) := by
  simp only [schouten_apply, LinearMap.smul_apply, LinearMap.sub_apply, innerₗ_apply_apply,
    ricci_compContinuousLinearMap_linearIsometryEquiv,
    scalar_compContinuousLinearMap_linearIsometryEquiv, e.toLinearEquiv.finrank_eq,
    e.inner_map_map]

theorem weyl_compContinuousLinearMap_linearIsometryEquiv (e : W ≃ₗᵢ[ℝ] V) (r : FourTensor V) :
    weyl (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      (weyl r).compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap := by
  ext m
  rw [weyl_apply, sub_apply, sub_apply,
    scalarPart_compContinuousLinearMap_linearIsometryEquiv e r,
    tracelessRicciPart_compContinuousLinearMap_linearIsometryEquiv e r]
  simp [weyl_apply]

end Equivariance

/-! ### Contraction adjointness, pairwise orthogonality, and the Pythagorean identity -/

section Orthogonality

variable {ι : Type*} [Fintype ι]

omit [FiniteDimensional ℝ V] in
private theorem sum_inner_mul_apply (b : OrthonormalBasis ι ℝ V) (d : ι) (F : ι → ℝ) :
    (∑ e, ⟪b d, b e⟫ * F e) = F d := by
  classical
  simp [orthonormal_iff_ite.mp b.orthonormal]

private theorem mul_ricci_eq_sum (b : OrthonormalBasis ι ℝ V) (q : FourTensor V)
    (c : ℝ) (u v : V) :
    c * ricci q u v = ∑ m, c * q ![b m, u, b m, v] := by
  rw [ricci_apply_orthonormalBasis b, Finset.mul_sum]

private theorem sum_four_mul (c : ℝ) (F : ι → ι → ι → ι → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, c * F i j k l) = c * ∑ i, ∑ j, ∑ k, ∑ l, F i j k l := by
  simp_rw [Finset.mul_sum]

private theorem tracelessRicciPart_antisymm_first (r : FourTensor V) (u v z w : V) :
    tracelessRicciPart r ![u, v, z, w] = -tracelessRicciPart r ![v, u, z, w] := by
  rw [tracelessRicciPart_apply, smul_apply, smul_apply, kulkarniNomizu_antisymm_first, smul_neg]

private theorem tracelessRicciPart_antisymm_last (r : FourTensor V) (u v z w : V) :
    tracelessRicciPart r ![u, v, z, w] = -tracelessRicciPart r ![u, v, w, z] := by
  rw [tracelessRicciPart_apply, smul_apply, smul_apply, kulkarniNomizu_antisymm_last, smul_neg]

private theorem sum_kn_term₁ (b : OrthonormalBasis ι ℝ V) (h : BilinForm ℝ V)
    {q : FourTensor V} (hq₁₂ : ∀ u v z w, q ![u, v, z, w] = q ![v, u, w, z]) :
    (∑ i, ∑ j, ∑ k, ∑ l, h (b i) (b k) * ⟪b j, b l⟫ * q ![b i, b j, b k, b l]) =
      ∑ i, ∑ k, h (b i) (b k) * ricci q (b i) (b k) := by
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [mul_ricci_eq_sum b q]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hmul (l : ι) :
      h (b i) (b k) * ⟪b j, b l⟫ * q ![b i, b j, b k, b l] =
        ⟪b j, b l⟫ * (h (b i) (b k) * q ![b i, b j, b k, b l]) := by ring
  simp_rw [hmul, sum_inner_mul_apply]
  rw [hq₁₂ (b i) (b j) (b k) (b j)]

private theorem sum_kn_term₂ (b : OrthonormalBasis ι ℝ V) (h : BilinForm ℝ V)
    (q : FourTensor V) :
    (∑ i, ∑ j, ∑ k, ∑ l, h (b j) (b l) * ⟪b i, b k⟫ * q ![b i, b j, b k, b l]) =
      ∑ j, ∑ l, h (b j) (b l) * ricci q (b j) (b l) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [mul_ricci_eq_sum b q]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hmul (k : ι) :
      h (b j) (b l) * ⟪b i, b k⟫ * q ![b i, b j, b k, b l] =
        ⟪b i, b k⟫ * (h (b j) (b l) * q ![b i, b j, b k, b l]) := by ring
  simp_rw [hmul, sum_inner_mul_apply]

private theorem sum_kn_term₃ (b : OrthonormalBasis ι ℝ V) (h : BilinForm ℝ V)
    {q : FourTensor V} (hq₁ : ∀ u v z w, q ![u, v, z, w] = -q ![v, u, z, w]) :
    (∑ i, ∑ j, ∑ k, ∑ l, h (b i) (b l) * ⟪b j, b k⟫ * q ![b i, b j, b k, b l]) =
      -∑ i, ∑ l, h (b i) (b l) * ricci q (b i) (b l) := by
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.sum_neg_distrib]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  have hneg : -(h (b i) (b l) * ricci q (b i) (b l)) =
      (-h (b i) (b l)) * ricci q (b i) (b l) := by ring
  rw [hneg, mul_ricci_eq_sum b q]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hmul (k : ι) :
      h (b i) (b l) * ⟪b j, b k⟫ * q ![b i, b j, b k, b l] =
        ⟪b j, b k⟫ * (h (b i) (b l) * q ![b i, b j, b k, b l]) := by ring
  simp_rw [hmul, sum_inner_mul_apply]
  rw [hq₁ (b i) (b j) (b j) (b l)]
  ring

private theorem sum_kn_term₄ (b : OrthonormalBasis ι ℝ V) (h : BilinForm ℝ V)
    {q : FourTensor V} (hq₂ : ∀ u v z w, q ![u, v, z, w] = -q ![u, v, w, z]) :
    (∑ i, ∑ j, ∑ k, ∑ l, h (b j) (b k) * ⟪b i, b l⟫ * q ![b i, b j, b k, b l]) =
      -∑ j, ∑ k, h (b j) (b k) * ricci q (b j) (b k) := by
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hneg : -(h (b j) (b k) * ricci q (b j) (b k)) =
      (-h (b j) (b k)) * ricci q (b j) (b k) := by ring
  rw [hneg, mul_ricci_eq_sum b q]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hmul (l : ι) :
      h (b j) (b k) * ⟪b i, b l⟫ * q ![b i, b j, b k, b l] =
        ⟪b i, b l⟫ * (h (b j) (b k) * q ![b i, b j, b k, b l]) := by ring
  simp_rw [hmul, sum_inner_mul_apply]
  rw [hq₂ (b i) (b j) (b k) (b i)]
  ring

/-- **Adjointness of `h ↦ h ⊙ g` and `ricci`**: in any orthonormal basis `(bᵢ)`, pairing
`kulkarniNomizu h (innerₗ V)` componentwise against any four-tensor `q` antisymmetric in both pairs
gives `4` times the componentwise pairing of `h` with `ricci q`. -/
theorem sum_kulkarniNomizu_innerₗ_mul (b : OrthonormalBasis ι ℝ V) (h : BilinForm ℝ V)
    {q : FourTensor V} (hq₁ : ∀ u v z w, q ![u, v, z, w] = -q ![v, u, z, w])
    (hq₂ : ∀ u v z w, q ![u, v, z, w] = -q ![u, v, w, z]) :
    (∑ i, ∑ j, ∑ k, ∑ l,
        kulkarniNomizu h (innerₗ V) ![b i, b j, b k, b l] * q ![b i, b j, b k, b l]) =
      4 * ∑ i, ∑ k, h (b i) (b k) * ricci q (b i) (b k) := by
  have hq₁₂ (u v z w : V) : q ![u, v, z, w] = q ![v, u, w, z] := by
    rw [hq₁ u v z w, hq₂ v u z w, neg_neg]
  simp only [kulkarniNomizu_apply, innerₗ_apply_apply, sub_mul, add_mul, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, sum_kn_term₁ b h hq₁₂, sum_kn_term₂ b h q, sum_kn_term₃ b h hq₁,
    sum_kn_term₄ b h hq₂]
  ring

theorem IsAlgebraicCurvature.sum_kulkarniNomizu_innerₗ_mul {q : FourTensor V}
    (hq : IsAlgebraicCurvature q) (b : OrthonormalBasis ι ℝ V) (h : BilinForm ℝ V) :
    (∑ i, ∑ j, ∑ k, ∑ l,
        kulkarniNomizu h (innerₗ V) ![b i, b j, b k, b l] * q ![b i, b j, b k, b l]) =
      4 * ∑ i, ∑ k, h (b i) (b k) * ricci q (b i) (b k) :=
  FourTensor.sum_kulkarniNomizu_innerₗ_mul b h hq.antisymm_first hq.antisymm_last

/-- Pairing `constantCurvature V` componentwise against a four-tensor `q` antisymmetric in its
first two arguments gives `2 * scalar q`. -/
theorem sum_constantCurvature_mul (b : OrthonormalBasis ι ℝ V) {q : FourTensor V}
    (hq₁ : ∀ u v z w, q ![u, v, z, w] = -q ![v, u, z, w]) :
    (∑ i, ∑ j, ∑ k, ∑ l,
        constantCurvature V ![b i, b j, b k, b l] * q ![b i, b j, b k, b l]) =
      2 * scalar q := by
  have hc (i j k l : ι) :
      constantCurvature V ![b i, b j, b k, b l] * q ![b i, b j, b k, b l] =
        innerₗ V (b j) (b l) * ⟪b i, b k⟫ * q ![b i, b j, b k, b l] -
          innerₗ V (b i) (b l) * ⟪b j, b k⟫ * q ![b i, b j, b k, b l] := by
    simp only [constantCurvature_apply, innerₗ_apply_apply]
    ring
  have htr : (∑ i, ∑ k, innerₗ V (b i) (b k) * ricci q (b i) (b k)) = scalar q := by
    simp only [innerₗ_apply_apply, sum_inner_mul_apply, ← bilinFormTrace_eq_sum (ricci q) b,
      ← scalar_apply]
  simp only [hc, Finset.sum_sub_distrib, sum_kn_term₂ b (innerₗ V) q,
    sum_kn_term₃ b (innerₗ V) hq₁, htr]
  ring

theorem sum_constantCurvature_sq (b : OrthonormalBasis ι ℝ V) :
    (∑ i, ∑ j, ∑ k, ∑ l, constantCurvature V ![b i, b j, b k, b l] ^ 2) =
      2 * (Module.finrank ℝ V : ℝ) * ((Module.finrank ℝ V : ℝ) - 1) := by
  have hc := isAlgebraicCurvature_constantCurvature (V := V)
  simp only [sq]
  rw [sum_constantCurvature_mul b hc.antisymm_first, scalar_constantCurvature, mul_assoc]

/-- The squared component norm of `scalarPart r` in any orthonormal basis is
`2 * scalar r ^ 2 / (n (n - 1))`. -/
theorem sum_scalarPart_sq (r : FourTensor V) (b : OrthonormalBasis ι ℝ V) :
    (∑ i, ∑ j, ∑ k, ∑ l, scalarPart r ![b i, b j, b k, b l] ^ 2) =
      2 * scalar r ^ 2 / ((Module.finrank ℝ V : ℝ) * ((Module.finrank ℝ V : ℝ) - 1)) := by
  rcases le_or_gt (Module.finrank ℝ V) 1 with hn | hn
  · have hc : constantCurvature V = 0 :=
      isAlgebraicCurvature_constantCurvature.eq_zero_of_finrank_le_one hn
    have hden : (Module.finrank ℝ V : ℝ) * ((Module.finrank ℝ V : ℝ) - 1) = 0 := by
      have : Module.finrank ℝ V = 0 ∨ Module.finrank ℝ V = 1 := by omega
      rcases this with h0 | h1
      · simp [h0]
      · simp [h1]
    simp [scalarPart_apply, hc, hden]
  · have hn0 : (Module.finrank ℝ V : ℝ) ≠ 0 := by positivity
    have hn1 : (Module.finrank ℝ V : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ Module.finrank ℝ V := by exact_mod_cast hn
      linarith
    have hpull :
        (∑ i, ∑ j, ∑ k, ∑ l, scalarPart r ![b i, b j, b k, b l] ^ 2) =
          (scalar r / ((Module.finrank ℝ V : ℝ) * ((Module.finrank ℝ V : ℝ) - 1))) ^ 2 *
            ∑ i, ∑ j, ∑ k, ∑ l, constantCurvature V ![b i, b j, b k, b l] ^ 2 := by
      simp only [scalarPart_apply, smul_apply, smul_eq_mul, mul_pow]
      exact sum_four_mul _ _
    rw [hpull, sum_constantCurvature_sq b]
    field_simp

/-- The squared component norm of `tracelessRicciPart r` in any orthonormal basis is
`(4 / (n - 2)) * ∑ i, ∑ k, tracelessRicci r (b i) (b k) ^ 2`. -/
theorem sum_tracelessRicciPart_sq (r : FourTensor V) (b : OrthonormalBasis ι ℝ V) :
    (∑ i, ∑ j, ∑ k, ∑ l, tracelessRicciPart r ![b i, b j, b k, b l] ^ 2) =
      (4 / ((Module.finrank ℝ V : ℝ) - 2)) *
        ∑ i, ∑ k, tracelessRicci r (b i) (b k) ^ 2 := by
  rcases eq_or_ne (Module.finrank ℝ V) 2 with hn2 | hn2
  · simp [tracelessRicciPart_apply, hn2]
  · have hpull :
        (∑ i, ∑ j, ∑ k, ∑ l, tracelessRicciPart r ![b i, b j, b k, b l] ^ 2) =
          ((Module.finrank ℝ V : ℝ) - 2)⁻¹ *
            ∑ i, ∑ j, ∑ k, ∑ l,
              kulkarniNomizu (tracelessRicci r) (innerₗ V) ![b i, b j, b k, b l] *
                tracelessRicciPart r ![b i, b j, b k, b l] := by
      rw [← sum_four_mul]
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
        Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
      rw [sq, tracelessRicciPart_apply, smul_apply, smul_eq_mul, mul_assoc]
    rw [hpull, sum_kulkarniNomizu_innerₗ_mul b (tracelessRicci r)
      (tracelessRicciPart_antisymm_first r) (tracelessRicciPart_antisymm_last r),
      ricci_tracelessRicciPart_of_ne_two hn2 r]
    simp only [← sq]
    ring

/-- The scalar part of any four-tensor is orthogonal to the trace-free Ricci part of any
four-tensor. -/
theorem sum_scalarPart_mul_tracelessRicciPart (r q : FourTensor V)
    (b : OrthonormalBasis ι ℝ V) :
    (∑ i, ∑ j, ∑ k, ∑ l,
        scalarPart r ![b i, b j, b k, b l] *
          tracelessRicciPart q ![b i, b j, b k, b l]) = 0 := by
  have hpull :
      (∑ i, ∑ j, ∑ k, ∑ l,
          scalarPart r ![b i, b j, b k, b l] *
            tracelessRicciPart q ![b i, b j, b k, b l]) =
        (scalar r / ((Module.finrank ℝ V : ℝ) * ((Module.finrank ℝ V : ℝ) - 1))) *
          ∑ i, ∑ j, ∑ k, ∑ l,
            constantCurvature V ![b i, b j, b k, b l] *
              tracelessRicciPart q ![b i, b j, b k, b l] := by
    simp only [scalarPart_apply, smul_apply, smul_eq_mul, mul_assoc]
    exact sum_four_mul _ _
  rw [hpull, sum_constantCurvature_mul b (tracelessRicciPart_antisymm_first q),
    scalar_tracelessRicciPart, mul_zero, mul_zero]

/-- The scalar part of any four-tensor is orthogonal to the Weyl part of any algebraic curvature
tensor. -/
theorem IsAlgebraicCurvature.sum_scalarPart_mul_weyl (r : FourTensor V) {q : FourTensor V}
    (hq : IsAlgebraicCurvature q) (b : OrthonormalBasis ι ℝ V) :
    (∑ i, ∑ j, ∑ k, ∑ l,
        scalarPart r ![b i, b j, b k, b l] * FourTensor.weyl q ![b i, b j, b k, b l]) = 0 := by
  have hw := hq.weyl
  have hpull :
      (∑ i, ∑ j, ∑ k, ∑ l,
          scalarPart r ![b i, b j, b k, b l] * FourTensor.weyl q ![b i, b j, b k, b l]) =
        (scalar r / ((Module.finrank ℝ V : ℝ) * ((Module.finrank ℝ V : ℝ) - 1))) *
          ∑ i, ∑ j, ∑ k, ∑ l,
            constantCurvature V ![b i, b j, b k, b l] *
              FourTensor.weyl q ![b i, b j, b k, b l] := by
    simp only [scalarPart_apply, smul_apply, smul_eq_mul, mul_assoc]
    exact sum_four_mul _ _
  rw [hpull, sum_constantCurvature_mul b hw.antisymm_first, hq.scalar_weyl, mul_zero, mul_zero]

/-- The trace-free Ricci part of any four-tensor is orthogonal to the Weyl part of any algebraic
curvature tensor. -/
theorem IsAlgebraicCurvature.sum_tracelessRicciPart_mul_weyl (r : FourTensor V)
    {q : FourTensor V} (hq : IsAlgebraicCurvature q) (b : OrthonormalBasis ι ℝ V) :
    (∑ i, ∑ j, ∑ k, ∑ l,
        FourTensor.tracelessRicciPart r ![b i, b j, b k, b l] *
          FourTensor.weyl q ![b i, b j, b k, b l]) = 0 := by
  have hw := hq.weyl
  have hpull :
      (∑ i, ∑ j, ∑ k, ∑ l,
          FourTensor.tracelessRicciPart r ![b i, b j, b k, b l] *
            FourTensor.weyl q ![b i, b j, b k, b l]) =
        ((Module.finrank ℝ V : ℝ) - 2)⁻¹ *
          ∑ i, ∑ j, ∑ k, ∑ l,
            kulkarniNomizu (tracelessRicci r) (innerₗ V) ![b i, b j, b k, b l] *
              FourTensor.weyl q ![b i, b j, b k, b l] := by
    simp only [tracelessRicciPart_apply, smul_apply, smul_eq_mul, mul_assoc]
    exact sum_four_mul _ _
  rw [hpull, hw.sum_kulkarniNomizu_innerₗ_mul b (tracelessRicci r), hq.ricci_weyl]
  simp

/-- **Pythagorean decomposition of an algebraic curvature tensor**: in any orthonormal basis, the
squared component norm of `r` is the sum of the squared component norms of its scalar, trace-free
Ricci, and Weyl parts. -/
theorem IsAlgebraicCurvature.sum_sq_eq_add {r : FourTensor V} (hr : IsAlgebraicCurvature r)
    (b : OrthonormalBasis ι ℝ V) :
    (∑ i, ∑ j, ∑ k, ∑ l, r ![b i, b j, b k, b l] ^ 2) =
      (∑ i, ∑ j, ∑ k, ∑ l, scalarPart r ![b i, b j, b k, b l] ^ 2) +
        (∑ i, ∑ j, ∑ k, ∑ l, FourTensor.tracelessRicciPart r ![b i, b j, b k, b l] ^ 2) +
        (∑ i, ∑ j, ∑ k, ∑ l, FourTensor.weyl r ![b i, b j, b k, b l] ^ 2) := by
  have hexp (i j k l : ι) :
      r ![b i, b j, b k, b l] ^ 2 =
        (scalarPart r ![b i, b j, b k, b l] ^ 2 +
          FourTensor.tracelessRicciPart r ![b i, b j, b k, b l] ^ 2 +
          FourTensor.weyl r ![b i, b j, b k, b l] ^ 2) +
          2 * (scalarPart r ![b i, b j, b k, b l] *
            FourTensor.tracelessRicciPart r ![b i, b j, b k, b l]) +
          2 * (scalarPart r ![b i, b j, b k, b l] *
            FourTensor.weyl r ![b i, b j, b k, b l]) +
          2 * (FourTensor.tracelessRicciPart r ![b i, b j, b k, b l] *
            FourTensor.weyl r ![b i, b j, b k, b l]) := by
    conv_lhs => rw [← scalarPart_add_tracelessRicciPart_add_weyl r]
    simp only [add_apply]
    ring
  simp only [hexp, Finset.sum_add_distrib, sum_four_mul,
    sum_scalarPart_mul_tracelessRicciPart r r b, hr.sum_scalarPart_mul_weyl r b,
    hr.sum_tracelessRicciPart_mul_weyl r b, mul_zero, add_zero]

/-- **Explicit norm-squared identity for algebraic curvature tensors**:
`∑ |r|² = (2 / (n (n - 1))) Scal(r)² + (4 / (n - 2)) ∑ |Ric₀(r)|² + ∑ |Weyl(r)|²`. -/
theorem IsAlgebraicCurvature.sum_sq_eq_scalar_add_tracelessRicci_add_weyl {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (b : OrthonormalBasis ι ℝ V) :
    (∑ i, ∑ j, ∑ k, ∑ l, r ![b i, b j, b k, b l] ^ 2) =
      2 * scalar r ^ 2 / ((Module.finrank ℝ V : ℝ) * ((Module.finrank ℝ V : ℝ) - 1)) +
        (4 / ((Module.finrank ℝ V : ℝ) - 2)) *
          (∑ i, ∑ k, tracelessRicci r (b i) (b k) ^ 2) +
        (∑ i, ∑ j, ∑ k, ∑ l, FourTensor.weyl r ![b i, b j, b k, b l] ^ 2) := by
  rw [hr.sum_sq_eq_add b, sum_scalarPart_sq r b, sum_tracelessRicciPart_sq r b]

end Orthogonality

end FourTensor

end TauCeti

end
