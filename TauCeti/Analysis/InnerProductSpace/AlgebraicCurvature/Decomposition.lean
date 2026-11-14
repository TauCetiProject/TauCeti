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
tensor `r` decomposes into three `O(V)`-equivariant, pairwise orthogonal algebraic curvature parts:
`r = scalarPart r + tracelessRicciPart r + weyl r`, where
* `scalarPart r = (scalar r / (n (n - 1))) • constantCurvature V` acts on `⋀[ℝ]^2 V` as
  `(scalar r / (n (n - 1))) • Id`;
* `tracelessRicciPart r = (n - 2)⁻¹ • kulkarniNomizu (tracelessRicci r) (innerₗ V)` carries
  `tracelessRicci r = ricci r - (scalar r / n) • innerₗ V` and acts on `⋀[ℝ]^2 V` as
  `(2 / (n - 2)) • wedgeEnd (tracelessRicciEnd r) Id`;
* `weyl r = r - scalarPart r - tracelessRicciPart r` is Ricci- and scalar-flat in all dimensions,
  equals `r - kulkarniNomizu (schouten r) (innerₗ V)` for `n ≠ 2`, and vanishes for `n ≤ 3`.

Pairing `h ⊙ g` against a skew-pair four-tensor `q` in an orthonormal basis `(bᵢ)` gives
`4 ∑ i k, h(bᵢ, bₖ) Ric(q)(bᵢ, bₖ)`, yielding pairwise orthogonality and the norm identity
`∑ |r|² = (2 / (n (n - 1))) Scal(r)² + (4 / (n - 2)) ∑ |Ric₀(r)|² + ∑ |Weyl(r)|²`.

## Main definitions

* `TauCeti.FourTensor.ricciEnd`, `TauCeti.FourTensor.tracelessRicci`,
  `TauCeti.FourTensor.tracelessRicciEnd`.
* `TauCeti.FourTensor.scalarPart`, `TauCeti.FourTensor.tracelessRicciPart`,
  `TauCeti.FourTensor.schouten`, `TauCeti.FourTensor.weyl`.

## Main statements

* `TauCeti.FourTensor.curvatureOperator_scalarPart`,
  `TauCeti.FourTensor.IsAlgebraicCurvature.curvatureOperator_tracelessRicciPart`,
  `TauCeti.FourTensor.IsAlgebraicCurvature.curvatureOperator_eq`.
* `TauCeti.FourTensor.IsAlgebraicCurvature.ricci_weyl`,
  `TauCeti.FourTensor.IsAlgebraicCurvature.scalar_weyl`, `TauCeti.FourTensor.weyl_weyl`,
  `TauCeti.FourTensor.weyl_kulkarniNomizu_innerₗ`,
  `TauCeti.FourTensor.weyl_eq_sub_kulkarniNomizu_schouten`,
  `TauCeti.FourTensor.IsAlgebraicCurvature.weyl_eq_zero_of_finrank_le_three`.
* `TauCeti.FourTensor.sum_kulkarniNomizu_innerₗ_mul`,
  `TauCeti.FourTensor.IsAlgebraicCurvature.sum_sq_eq_add`,
  `TauCeti.FourTensor.IsAlgebraicCurvature.sum_sq_eq_scalar_add_tracelessRicci_add_weyl`.

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

private theorem vec4_eta {α : Type*} (m : Fin 4 → α) : m = ![m 0, m 1, m 2, m 3] := by
  funext i; fin_cases i <;> rfl

private theorem constantCurvature_eq_smul_kulkarniNomizu :
    constantCurvature V = (1 / 2 : ℝ) • kulkarniNomizu (innerₗ V) (innerₗ V) := by
  ext m; rw [vec4_eta m]; simp [constantCurvature_apply, kulkarniNomizu_apply]; ring

omit [FiniteDimensional ℝ V] in
private theorem isSymm_innerₗ (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] :
    LinearMap.BilinForm.IsSymm (innerₗ V) :=
  ⟨fun u v ↦ real_inner_comm v u⟩

omit [FiniteDimensional ℝ V] in
private theorem finrank_sub_one_ne_zero (h : Module.finrank ℝ V ≠ 1) :
    (Module.finrank ℝ V : ℝ) - 1 ≠ 0 :=
  sub_ne_zero.mpr (by exact_mod_cast h)

omit [FiniteDimensional ℝ V] in
private theorem finrank_sub_two_ne_zero (h : Module.finrank ℝ V ≠ 2) :
    (Module.finrank ℝ V : ℝ) - 2 ≠ 0 :=
  sub_ne_zero.mpr (by exact_mod_cast h)

private theorem eq_zero_of_finrank_eq_zero (hn : Module.finrank ℝ V = 0) (r : FourTensor V) :
    r = 0 := by
  have : Subsingleton V := Module.finrank_zero_iff.mp hn
  ext m; exact r.map_coord_zero (0 : Fin 4) (Subsingleton.elim (m 0) 0)

private theorem bilinForm_eq_zero_of_finrank_eq_zero (hn : Module.finrank ℝ V = 0)
    (B : BilinForm ℝ V) : B = 0 := by
  have : Subsingleton V := Module.finrank_zero_iff.mp hn
  ext u v; rw [Subsingleton.elim u 0]; simp

private theorem kulkarniNomizu_antisymm_first (h k : BilinForm ℝ V) (u v z w : V) :
    kulkarniNomizu h k ![u, v, z, w] = -kulkarniNomizu h k ![v, u, z, w] := by
  simpa only [kulkarniNomizu_apply_eq] using LinearMap.BilinForm.kulkarniNomizu_antisymm_first ..

private theorem kulkarniNomizu_antisymm_last (h k : BilinForm ℝ V) (u v z w : V) :
    kulkarniNomizu h k ![u, v, z, w] = -kulkarniNomizu h k ![u, v, w, z] := by
  simpa only [kulkarniNomizu_apply_eq] using LinearMap.BilinForm.kulkarniNomizu_antisymm_last ..

private theorem eq_zero_of_antisymm_first_of_finrank_le_one (hn : Module.finrank ℝ V ≤ 1)
    {q : FourTensor V} (hq₁ : ∀ u v z w, q ![u, v, z, w] = -q ![v, u, z, w]) : q = 0 := by
  apply toLinearMap₄_injective; rw [map_zero]
  let b := (stdOrthonormalBasis ℝ V).toBasis
  refine b.ext fun i ↦ b.ext fun j ↦ b.ext fun k ↦ b.ext fun l ↦ ?_
  rw [show i = j from Fin.ext (by omega)]
  simp only [toLinearMap₄_apply, LinearMap.zero_apply]; linarith [hq₁ (b j) (b j) (b k) (b l)]

private theorem eq_smul_constantCurvature_of_antisymm_of_finrank_eq_two
    (hn : Module.finrank ℝ V = 2) {q : FourTensor V}
    (hq₁ : ∀ u v z w, q ![u, v, z, w] = -q ![v, u, z, w])
    (hq₂ : ∀ u v z w, q ![u, v, z, w] = -q ![u, v, w, z]) :
    q = q ![(stdOrthonormalBasis ℝ V).reindex (finCongr hn) 0,
      (stdOrthonormalBasis ℝ V).reindex (finCongr hn) 1,
      (stdOrthonormalBasis ℝ V).reindex (finCongr hn) 0,
      (stdOrthonormalBasis ℝ V).reindex (finCongr hn) 1] • constantCurvature V := by
  set b := (stdOrthonormalBasis ℝ V).reindex (finCongr hn)
  have hf0 : (⟨0, by decide⟩ : Fin 2) = 0 := rfl
  have hf1 : (⟨1, by decide⟩ : Fin 2) = 1 := rfl
  apply toLinearMap₄_injective
  refine b.toBasis.ext fun i ↦ b.toBasis.ext fun j ↦
    b.toBasis.ext fun k ↦ b.toBasis.ext fun l ↦ ?_
  simp only [OrthonormalBasis.coe_toBasis, map_smul, LinearMap.smul_apply, toLinearMap₄_apply,
    constantCurvature_apply, smul_eq_mul]
  by_cases hij : i = j
  · rw [hij]; ring_nf; linarith [hq₁ (b j) (b j) (b k) (b l)]
  by_cases hkl : k = l
  · rw [hkl]; ring_nf; linarith [hq₂ (b i) (b j) (b l) (b l)]
  fin_cases i <;> fin_cases j <;> try exact absurd rfl hij
  all_goals fin_cases k <;> fin_cases l <;> try exact absurd rfl hkl
  all_goals simp only [hf0, hf1, orthonormal_iff_ite.mp b.orthonormal, ↓reduceIte,
    (by decide : (0 : Fin 2) ≠ 1), (by decide : (1 : Fin 2) ≠ 0)]
  · ring
  · linarith [hq₂ (b 0) (b 1) (b 1) (b 0)]
  · linarith [hq₁ (b 1) (b 0) (b 0) (b 1)]
  · linarith [hq₁ (b 1) (b 0) (b 1) (b 0), hq₂ (b 0) (b 1) (b 1) (b 0)]

/-! ### The Ricci and trace-free Ricci endomorphisms -/

/-- The Ricci endomorphism on `V` associated with a four-tensor `r`, characterized by
`⟪ricciEnd r u, v⟫ = ricci r u v`. -/
def ricciEnd : FourTensor V →ₗ[ℝ] Module.End ℝ V where
  toFun r := (ricci r).symmCompOfNondegenerate (innerₗ V) TauCeti.nondegenerate_inner
  map_add' _ _ := LinearMap.ext fun _ ↦ ext_inner_right ℝ fun _ ↦ by
    simp [inner_add_left, ← innerₗ_apply_apply]
  map_smul' _ _ := LinearMap.ext fun _ ↦ ext_inner_right ℝ fun _ ↦ by
    simp [← innerₗ_apply_apply]

@[simp]
theorem inner_ricciEnd_left (r : FourTensor V) (u v : V) :
    ⟪ricciEnd r u, v⟫ = ricci r u v :=
  LinearMap.BilinForm.symmCompOfNondegenerate_left_apply (ricci r) TauCeti.nondegenerate_inner v u

theorem innerₗ_comp_ricciEnd (r : FourTensor V) : innerₗ V ∘ₗ ricciEnd r = ricci r :=
  LinearMap.ext₂ (inner_ricciEnd_left r)

theorem IsAlgebraicCurvature.isSymmetric_ricciEnd {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) : (ricciEnd r).IsSymmetric := fun u v ↦ by
  rw [inner_ricciEnd_left, real_inner_comm, inner_ricciEnd_left, hr.isSymm_ricci.eq]

theorem IsAlgebraicCurvature.inner_ricciEnd_right {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (u v : V) : ⟪u, ricciEnd r v⟫ = ricci r u v := by
  rw [← hr.isSymmetric_ricciEnd u v, inner_ricciEnd_left]

@[simp]
theorem trace_ricciEnd (r : FourTensor V) : LinearMap.trace ℝ V (ricciEnd r) = scalar r := by
  let b := stdOrthonormalBasis ℝ V
  rw [LinearMap.trace_eq_sum_inner _ b, scalar_apply, bilinFormTrace_eq_sum _ b]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [real_inner_comm, inner_ricciEnd_left]

@[simp]
theorem ricciEnd_constantCurvature :
    ricciEnd (constantCurvature V) = ((Module.finrank ℝ V : ℝ) - 1) • LinearMap.id :=
  LinearMap.ext fun _ ↦ ext_inner_right ℝ fun _ ↦ by
    simp [ricci_constantCurvature, real_inner_smul_left]

/-- The trace-free Ricci bilinear form `Ric₀(r) = Ric(r) - (Scal(r) / n) g`. -/
def tracelessRicci : FourTensor V →ₗ[ℝ] BilinForm ℝ V where
  toFun r := ricci r - (scalar r / Module.finrank ℝ V) • innerₗ V
  map_add' _ _ := by
    ext; simp only [map_add, add_div, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.smul_apply, innerₗ_apply_apply, smul_eq_mul]; ring
  map_smul' _ _ := by
    ext; simp only [map_smul, RingHom.id_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      innerₗ_apply_apply, smul_eq_mul, mul_div_assoc]; ring

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
  · let b := stdOrthonormalBasis ℝ V
    rw [bilinFormTrace_eq_sum _ b]
    simp [Finset.sum_sub_distrib, ← bilinFormTrace_eq_sum (ricci r) b, ← scalar_apply,
      mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hn : (Module.finrank ℝ V : ℝ) ≠ 0)]

theorem IsAlgebraicCurvature.isSymm_tracelessRicci {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) : (tracelessRicci r).IsSymm :=
  ⟨fun u v ↦ by simp [hr.isSymm_ricci.eq u v, real_inner_comm u v]⟩

@[simp]
theorem tracelessRicci_constantCurvature : tracelessRicci (constantCurvature V) = 0 := by
  rcases eq_or_ne (Module.finrank ℝ V) 0 with hn | hn
  · exact bilinForm_eq_zero_of_finrank_eq_zero hn _
  · ext u v
    simp [ricci_constantCurvature, scalar_constantCurvature,
      mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hn : (Module.finrank ℝ V : ℝ) ≠ 0)]

/-- The trace-free Ricci endomorphism `ricciEnd r - (scalar r / n) • Id` on `V`. -/
def tracelessRicciEnd : FourTensor V →ₗ[ℝ] Module.End ℝ V :=
  ricciEnd (V := V) - ((Module.finrank ℝ V : ℝ)⁻¹ • scalar (V := V)).smulRight LinearMap.id

theorem tracelessRicciEnd_apply (r : FourTensor V) :
    tracelessRicciEnd r = ricciEnd r - (scalar r / Module.finrank ℝ V) • LinearMap.id := by
  ext u; simp [tracelessRicciEnd, div_eq_inv_mul]

@[simp]
theorem inner_tracelessRicciEnd_left (r : FourTensor V) (u v : V) :
    ⟪tracelessRicciEnd r u, v⟫ = tracelessRicci r u v := by
  simp [tracelessRicciEnd_apply, inner_sub_left, real_inner_smul_left]

theorem innerₗ_comp_tracelessRicciEnd (r : FourTensor V) :
    innerₗ V ∘ₗ tracelessRicciEnd r = tracelessRicci r :=
  LinearMap.ext₂ (inner_tracelessRicciEnd_left r)

theorem IsAlgebraicCurvature.isSymmetric_tracelessRicciEnd {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) : (tracelessRicciEnd r).IsSymmetric := fun u v ↦ by
  rw [inner_tracelessRicciEnd_left, real_inner_comm, inner_tracelessRicciEnd_left,
    hr.isSymm_tracelessRicci.eq]

@[simp]
theorem trace_tracelessRicciEnd (r : FourTensor V) :
    LinearMap.trace ℝ V (tracelessRicciEnd r) = 0 := by
  let b := stdOrthonormalBasis ℝ V
  rw [LinearMap.trace_eq_sum_inner _ b, ← bilinFormTrace_tracelessRicci r,
    bilinFormTrace_eq_sum _ b]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [real_inner_comm, inner_tracelessRicciEnd_left]

@[simp]
theorem tracelessRicciEnd_constantCurvature : tracelessRicciEnd (constantCurvature V) = 0 :=
  LinearMap.ext fun _ ↦ ext_inner_right ℝ fun _ ↦ by simp

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
  ext; simp [scalarPart, div_eq_inv_mul]

theorem isAlgebraicCurvature_scalarPart (r : FourTensor V) :
    IsAlgebraicCurvature (scalarPart r) :=
  scalarPart_apply r ▸ mem_algebraicCurvatureSubmodule.mp
    ((algebraicCurvatureSubmodule V).smul_mem _
      (mem_algebraicCurvatureSubmodule.mpr isAlgebraicCurvature_constantCurvature))

/-- The trace-free Ricci component `(n - 2)⁻¹ • kulkarniNomizu (tracelessRicci r) (innerₗ V)` of a
four-tensor. -/
def tracelessRicciPart : FourTensor V →ₗ[ℝ] FourTensor V :=
  ((Module.finrank ℝ V : ℝ) - 2)⁻¹ • (kulkarniNomizu.flip (innerₗ V) ∘ₗ tracelessRicci (V := V))

theorem tracelessRicciPart_apply (r : FourTensor V) :
    tracelessRicciPart r =
      ((Module.finrank ℝ V : ℝ) - 2)⁻¹ • kulkarniNomizu (tracelessRicci r) (innerₗ V) :=
  (rfl)

theorem IsAlgebraicCurvature.tracelessRicciPart {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) : IsAlgebraicCurvature (FourTensor.tracelessRicciPart r) :=
  mem_algebraicCurvatureSubmodule.mp ((algebraicCurvatureSubmodule V).smul_mem _
    (mem_algebraicCurvatureSubmodule.mpr
      (isAlgebraicCurvature_kulkarniNomizu hr.isSymm_tracelessRicci (isSymm_innerₗ V))))

/-- The Schouten bilinear form `P(r) = (n - 2)⁻¹ • (Ric(r) - (Scal(r) / (2 (n - 1))) g)`. -/
def schouten : FourTensor V →ₗ[ℝ] BilinForm ℝ V where
  toFun r := ((Module.finrank ℝ V : ℝ) - 2)⁻¹ •
    (ricci r - (scalar r / (2 * ((Module.finrank ℝ V : ℝ) - 1))) • innerₗ V)
  map_add' _ _ := by
    ext; simp only [map_add, add_div, LinearMap.smul_apply, LinearMap.sub_apply,
      LinearMap.add_apply, innerₗ_apply_apply, smul_eq_mul]; ring
  map_smul' _ _ := by
    ext; simp only [map_smul, RingHom.id_apply, LinearMap.smul_apply, LinearMap.sub_apply,
      innerₗ_apply_apply, smul_eq_mul, mul_div_assoc]; ring

theorem schouten_apply (r : FourTensor V) :
    schouten r =
      ((Module.finrank ℝ V : ℝ) - 2)⁻¹ •
        (ricci r - (scalar r / (2 * ((Module.finrank ℝ V : ℝ) - 1))) • innerₗ V) :=
  (rfl)

theorem IsAlgebraicCurvature.isSymm_schouten {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    (schouten r).IsSymm :=
  ⟨fun u v ↦ by simp [schouten_apply, hr.isSymm_ricci.eq u v, real_inner_comm u v]⟩

/-- The Weyl component `r - scalarPart r - tracelessRicciPart r` of a four-tensor. -/
def weyl : FourTensor V →ₗ[ℝ] FourTensor V :=
  LinearMap.id - scalarPart - tracelessRicciPart

theorem weyl_apply (r : FourTensor V) : weyl r = r - scalarPart r - tracelessRicciPart r :=
  (rfl)

/-- **Ricci–Weyl decomposition**: every four-tensor is the sum of its scalar, trace-free Ricci, and
Weyl parts. -/
theorem scalarPart_add_tracelessRicciPart_add_weyl (r : FourTensor V) :
    scalarPart r + tracelessRicciPart r + weyl r = r := by rw [weyl_apply]; abel

theorem IsAlgebraicCurvature.weyl {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    IsAlgebraicCurvature (FourTensor.weyl r) :=
  mem_algebraicCurvatureSubmodule.mp ((algebraicCurvatureSubmodule V).sub_mem
    ((algebraicCurvatureSubmodule V).sub_mem (mem_algebraicCurvatureSubmodule.mpr hr)
      (mem_algebraicCurvatureSubmodule.mpr (isAlgebraicCurvature_scalarPart r)))
    (mem_algebraicCurvatureSubmodule.mpr hr.tracelessRicciPart))

/-! ### Bivector curvature operators of the decomposition pieces -/

/-- The scalar curvature component acts on `⋀[ℝ]^2 V` as `(scalar r / (n (n - 1))) • Id`. -/
@[simp]
theorem curvatureOperator_scalarPart (r : FourTensor V) :
    curvatureOperator ⟨scalarPart r, mem_algebraicCurvatureSubmodule.mpr
      (isAlgebraicCurvature_scalarPart r)⟩ =
      (scalar r / ((Module.finrank ℝ V : ℝ) * ((Module.finrank ℝ V : ℝ) - 1))) •
        LinearMap.id := by
  have hs : (⟨scalarPart r, mem_algebraicCurvatureSubmodule.mpr
      (isAlgebraicCurvature_scalarPart r)⟩ : algebraicCurvatureSubmodule V) =
    (scalar r / ((Module.finrank ℝ V : ℝ) * ((Module.finrank ℝ V : ℝ) - 1))) •
      ⟨constantCurvature V,
        mem_algebraicCurvatureSubmodule.mpr isAlgebraicCurvature_constantCurvature⟩ :=
    Subtype.ext (scalarPart_apply r)
  rw [hs, map_smul, curvatureOperator_constantCurvature]

/-- The trace-free Ricci component of an algebraic curvature tensor acts on `⋀[ℝ]^2 V` as
`(2 / (n - 2)) • wedgeEnd (tracelessRicciEnd r) Id`. -/
theorem IsAlgebraicCurvature.curvatureOperator_tracelessRicciPart {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) :
    curvatureOperator ⟨FourTensor.tracelessRicciPart r,
        mem_algebraicCurvatureSubmodule.mpr hr.tracelessRicciPart⟩ =
      (2 / ((Module.finrank ℝ V : ℝ) - 2)) • wedgeEnd (tracelessRicciEnd r) LinearMap.id := by
  rw [curvatureOperator_eq_iff]; intro u v z w
  simp only [LinearMap.smul_apply, real_inner_smul_left, inner_wedgeEnd_ιMulti,
    innerₗ_comp_tracelessRicciEnd, LinearMap.comp_id, tracelessRicciPart_apply, smul_apply,
    smul_eq_mul]; ring

/-- **Bivector operator decomposition**: the curvature operator of `r` splits into its scalar
multiple of the identity, its symmetric wedge `(2 / (n - 2)) • (Ric₀ ∧ Id)`, and the Weyl operator
in every dimension. -/
theorem IsAlgebraicCurvature.curvatureOperator_eq {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) :
    curvatureOperator ⟨r, mem_algebraicCurvatureSubmodule.mpr hr⟩ =
      (scalar r / ((Module.finrank ℝ V : ℝ) * ((Module.finrank ℝ V : ℝ) - 1))) • LinearMap.id +
        (2 / ((Module.finrank ℝ V : ℝ) - 2)) • wedgeEnd (tracelessRicciEnd r) LinearMap.id +
        curvatureOperator ⟨FourTensor.weyl r, mem_algebraicCurvatureSubmodule.mpr hr.weyl⟩ := by
  have hsum : (⟨r, mem_algebraicCurvatureSubmodule.mpr hr⟩ : algebraicCurvatureSubmodule V) =
      ⟨scalarPart r, mem_algebraicCurvatureSubmodule.mpr (isAlgebraicCurvature_scalarPart r)⟩ +
        ⟨FourTensor.tracelessRicciPart r,
          mem_algebraicCurvatureSubmodule.mpr hr.tracelessRicciPart⟩ +
        ⟨FourTensor.weyl r, mem_algebraicCurvatureSubmodule.mpr hr.weyl⟩ :=
    Subtype.ext (scalarPart_add_tracelessRicciPart_add_weyl r).symm
  rw [hsum, map_add, map_add, curvatureOperator_scalarPart, hr.curvatureOperator_tracelessRicciPart]

/-! ### Contractions, idempotence, and mutual annihilation -/

@[simp]
theorem scalarPart_constantCurvature : scalarPart (constantCurvature V) = constantCurvature V := by
  rcases le_or_gt (Module.finrank ℝ V) 1 with hn | hn
  · simp [isAlgebraicCurvature_constantCurvature.eq_zero_of_finrank_le_one hn]
  · have hn0 : (Module.finrank ℝ V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [scalarPart_apply, scalar_constantCurvature,
      div_self (mul_ne_zero hn0 (finrank_sub_one_ne_zero (by omega))), one_smul]

@[simp]
theorem scalarPart_scalarPart (r : FourTensor V) : scalarPart (scalarPart r) = scalarPart r := by
  rw [scalarPart_apply r, map_smul, scalarPart_constantCurvature]

@[simp]
theorem tracelessRicci_scalarPart (r : FourTensor V) : tracelessRicci (scalarPart r) = 0 := by
  rw [scalarPart_apply, map_smul, tracelessRicci_constantCurvature, smul_zero]

@[simp]
theorem tracelessRicciPart_constantCurvature : tracelessRicciPart (constantCurvature V) = 0 := by
  simp [tracelessRicciPart_apply]

@[simp]
theorem tracelessRicciPart_scalarPart (r : FourTensor V) :
    tracelessRicciPart (scalarPart r) = 0 := by simp [tracelessRicciPart_apply]

theorem IsAlgebraicCurvature.ricci_scalarPart {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    ricci (scalarPart r) = (scalar r / Module.finrank ℝ V) • innerₗ V := by
  rcases le_or_gt (Module.finrank ℝ V) 1 with hn | hn
  · simp [hr.eq_zero_of_finrank_le_one hn]
  · have hn1 := finrank_sub_one_ne_zero (V := V) (by omega)
    rw [scalarPart_apply, map_smul, ricci_constantCurvature, smul_smul]; congr 1; field_simp

theorem IsAlgebraicCurvature.scalar_scalarPart {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    scalar (scalarPart r) = scalar r := by
  rcases eq_or_ne (Module.finrank ℝ V) 0 with hn | hn
  · simp [eq_zero_of_finrank_eq_zero hn r]
  · rw [scalar_apply, hr.ricci_scalarPart, map_smul, bilinFormTrace_inner, smul_eq_mul,
      div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hn)]

@[simp]
theorem scalar_tracelessRicciPart (r : FourTensor V) : scalar (tracelessRicciPart r) = 0 := by
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
  rw [tracelessRicciPart_apply, map_smul, ricci_kulkarniNomizu_innerₗ,
    bilinFormTrace_tracelessRicci, zero_smul, add_zero, smul_smul,
    inv_mul_cancel₀ (finrank_sub_two_ne_zero hn), one_smul]

theorem IsAlgebraicCurvature.ricci_tracelessRicciPart {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) :
    ricci (FourTensor.tracelessRicciPart r) = tracelessRicci r := by
  rcases eq_or_ne (Module.finrank ℝ V) 2 with hn2 | hn2
  · have htr : tracelessRicci r = 0 := by
      rw [hr.eq_smul_constantCurvature_of_finrank_eq_two hn2, map_smul,
        tracelessRicci_constantCurvature, smul_zero]
    rw [tracelessRicciPart_apply, hn2]; norm_num [htr]
  · exact ricci_tracelessRicciPart_of_ne_two hn2 r

theorem IsAlgebraicCurvature.tracelessRicci_tracelessRicciPart {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) :
    tracelessRicci (FourTensor.tracelessRicciPart r) = tracelessRicci r := by
  ext; simp [hr.ricci_tracelessRicciPart]

@[simp]
theorem tracelessRicciPart_tracelessRicciPart (r : FourTensor V) :
    tracelessRicciPart (tracelessRicciPart r) = tracelessRicciPart r := by
  rcases eq_or_ne (Module.finrank ℝ V) 2 with hn2 | hn2
  · simp [tracelessRicciPart_apply, hn2]
  · have hric : tracelessRicci (tracelessRicciPart r) = tracelessRicci r := by
      ext; simp [ricci_tracelessRicciPart_of_ne_two hn2 r]
    rw [tracelessRicciPart_apply (tracelessRicciPart r), hric, ← tracelessRicciPart_apply]

/-- **The Weyl part of every algebraic curvature tensor is Ricci-flat in all dimensions.** -/
theorem IsAlgebraicCurvature.ricci_weyl {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    ricci (FourTensor.weyl r) = 0 := by
  rw [weyl_apply, map_sub, map_sub, hr.ricci_scalarPart, hr.ricci_tracelessRicciPart,
    tracelessRicci_apply]; abel

/-- **The Weyl part of every algebraic curvature tensor has zero scalar contraction.** -/
theorem IsAlgebraicCurvature.scalar_weyl {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    scalar (FourTensor.weyl r) = 0 := by rw [scalar_apply, hr.ricci_weyl, map_zero]

theorem IsAlgebraicCurvature.tracelessRicci_weyl {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) : tracelessRicci (FourTensor.weyl r) = 0 := by
  ext; simp [hr.ricci_weyl, hr.scalar_weyl]

@[simp]
theorem scalarPart_weyl (r : FourTensor V) : scalarPart (weyl r) = 0 := by
  rcases le_or_gt (Module.finrank ℝ V) 1 with hn | hn
  · simp [scalarPart_apply, isAlgebraicCurvature_constantCurvature.eq_zero_of_finrank_le_one hn]
  · have hn0 : (Module.finrank ℝ V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hscal : scalar (scalarPart r) = scalar r := by
      rw [scalarPart_apply, map_smul, scalar_constantCurvature, smul_eq_mul,
        div_mul_cancel₀ _ (mul_ne_zero hn0 (finrank_sub_one_ne_zero (by omega)))]
    rw [scalarPart_apply, weyl_apply, map_sub, map_sub, hscal, scalar_tracelessRicciPart,
      sub_self, sub_zero, zero_div, zero_smul]

@[simp]
theorem tracelessRicciPart_weyl (r : FourTensor V) : tracelessRicciPart (weyl r) = 0 := by
  rcases eq_or_ne (Module.finrank ℝ V) 2 with hn2 | hn2
  · simp [tracelessRicciPart_apply, hn2]
  · have htr : tracelessRicci (tracelessRicciPart r) = tracelessRicci r := by
      ext; simp [ricci_tracelessRicciPart_of_ne_two hn2 r]
    have htr_weyl : tracelessRicci (weyl r) = 0 := by
      rw [weyl_apply, map_sub, map_sub, tracelessRicci_scalarPart, htr]; abel
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
  have : (Module.finrank ℝ V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have := finrank_sub_one_ne_zero (V := V) (by omega)
  have := finrank_sub_two_ne_zero (V := V) (by omega)
  ext u v
  simp only [schouten_apply, tracelessRicci_apply, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, innerₗ_apply_apply, smul_eq_mul]
  field_simp; ring

/-- Away from dimension `2`, the Kulkarni–Nomizu product of the Schouten tensor of any four-tensor
with the inner product equals `scalarPart r + tracelessRicciPart r`. -/
theorem kulkarniNomizu_schouten_innerₗ (hn : Module.finrank ℝ V ≠ 2) (r : FourTensor V) :
    kulkarniNomizu (schouten r) (innerₗ V) = scalarPart r + tracelessRicciPart r := by
  rcases lt_or_gt_of_ne hn with hnlt | hngt
  · have hkn (h k : BilinForm ℝ V) : kulkarniNomizu h k = 0 :=
      eq_zero_of_antisymm_first_of_finrank_le_one (by omega) (kulkarniNomizu_antisymm_first h k)
    simp [hkn, scalarPart_apply, constantCurvature_eq_smul_kulkarniNomizu, tracelessRicciPart_apply]
  · have : (Module.finrank ℝ V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have := finrank_sub_one_ne_zero (V := V) (by omega)
    rw [schouten_eq_add_of_three_le hngt r, map_add, LinearMap.add_apply, map_smul, map_smul,
      LinearMap.smul_apply, LinearMap.smul_apply, ← tracelessRicciPart_apply, scalarPart_apply,
      constantCurvature_eq_smul_kulkarniNomizu, smul_smul, add_comm]
    congr 2; field_simp

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
  · simp [hr.eq_zero_of_finrank_le_one (by omega)]
  · have : (Module.finrank ℝ V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have := finrank_sub_one_ne_zero (V := V) (by omega)
    rw [schouten_eq_add_of_three_le hngt r, map_add, map_smul, bilinFormTrace_tracelessRicci,
      smul_zero, zero_add, map_smul, bilinFormTrace_inner, smul_eq_mul]; field_simp

/-- In every dimension, `weyl (kulkarniNomizu h (innerₗ V)) = 0` for every bilinear form `h`. -/
@[simp]
theorem weyl_kulkarniNomizu_innerₗ (h : BilinForm ℝ V) :
    weyl (kulkarniNomizu h (innerₗ V)) = 0 := by
  rcases (by omega : Module.finrank ℝ V ≤ 1 ∨ Module.finrank ℝ V = 2 ∨ 3 ≤ Module.finrank ℝ V)
    with h1 | h2 | h3
  · rw [eq_zero_of_antisymm_first_of_finrank_le_one h1
      (kulkarniNomizu_antisymm_first h (innerₗ V)), map_zero]
  · rw [eq_smul_constantCurvature_of_antisymm_of_finrank_eq_two h2
      (kulkarniNomizu_antisymm_first h (innerₗ V)) (kulkarniNomizu_antisymm_last h (innerₗ V)),
      map_smul, weyl_constantCurvature, smul_zero]
  · have := finrank_sub_one_ne_zero (V := V) (by omega)
    have := finrank_sub_two_ne_zero (V := V) (by omega)
    have hsch : schouten (kulkarniNomizu h (innerₗ V)) = h := by
      ext u v
      simp only [schouten_apply, ricci_kulkarniNomizu_innerₗ, scalar_kulkarniNomizu_innerₗ,
        LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, innerₗ_apply_apply,
        smul_eq_mul]
      field_simp; ring
    rw [weyl_eq_sub_kulkarniNomizu_schouten (by omega), hsch, sub_self]

/-! ### Vanishing of the Weyl tensor in dimension at most three -/

/-- **In dimension `3`, the Weyl part of every algebraic curvature tensor vanishes.** -/
theorem IsAlgebraicCurvature.weyl_eq_zero_of_finrank_eq_three {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (hn : Module.finrank ℝ V = 3) :
    FourTensor.weyl r = 0 := by
  apply toLinearMap₄_injective; rw [map_zero]
  let b := stdOrthonormalBasis ℝ V
  have hw := hr.weyl
  refine LinearMap.eq_zero_of_sum_basis_eq_zero_of_card_eq_three
    (fun _ _ hxy ↦ by simp only [smul_eq_mul] at hxy; linarith) b.toBasis (by simp [hn])
    (fun x y z w ↦ by simp [hw.antisymm_first x y z w])
    (fun x y z w ↦ by simp [hw.antisymm_last x y z w]) fun y z ↦ ?_
  have hsum : ∑ i, FourTensor.weyl r ![b i, y, z, b i] = -ricci (FourTensor.weyl r) y z := by
    rw [ricci_apply_orthonormalBasis b, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ hw.antisymm_last (b i) y z (b i)
  simp [OrthonormalBasis.coe_toBasis, hsum, hr.ricci_weyl]

/-- **In dimension at most `3`, the Weyl part of every algebraic curvature tensor vanishes.** -/
theorem IsAlgebraicCurvature.weyl_eq_zero_of_finrank_le_three {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (hn : Module.finrank ℝ V ≤ 3) :
    FourTensor.weyl r = 0 := by
  rcases (by omega : Module.finrank ℝ V ≤ 1 ∨ Module.finrank ℝ V = 2 ∨ Module.finrank ℝ V = 3)
    with h1 | h2 | h3
  · rw [hr.eq_zero_of_finrank_le_one h1, map_zero]
  · rw [hr.eq_smul_constantCurvature_of_finrank_eq_two h2, map_smul, weyl_constantCurvature,
      smul_zero]
  · exact hr.weyl_eq_zero_of_finrank_eq_three h3

/-- In dimension at most `3`, every algebraic curvature tensor is recovered from its scalar and
trace-free Ricci parts: `r = scalarPart r + tracelessRicciPart r`. -/
theorem IsAlgebraicCurvature.eq_scalarPart_add_tracelessRicciPart_of_finrank_le_three
    {r : FourTensor V} (hr : IsAlgebraicCurvature r) (hn : Module.finrank ℝ V ≤ 3) :
    r = scalarPart r + FourTensor.tracelessRicciPart r := by
  simpa [hr.weyl_eq_zero_of_finrank_le_three hn] using
    (scalarPart_add_tracelessRicciPart_add_weyl r).symm

/-! ### Equivariance under linear isometric equivalences -/

section Equivariance

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

theorem tracelessRicci_compContinuousLinearMap_linearIsometryEquiv (e : W ≃ₗᵢ[ℝ] V)
    (r : FourTensor V) (u v : W) :
    tracelessRicci (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap)
        u v = tracelessRicci r (e u) (e v) := by
  simp [ricci_compContinuousLinearMap_linearIsometryEquiv,
    scalar_compContinuousLinearMap_linearIsometryEquiv, e.toLinearEquiv.finrank_eq]

theorem ricciEnd_compContinuousLinearMap_linearIsometryEquiv (e : W ≃ₗᵢ[ℝ] V)
    (r : FourTensor V) :
    ricciEnd (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      e.toLinearEquiv.symm.conj (ricciEnd r) :=
  LinearMap.ext fun u ↦ ext_inner_right ℝ fun v ↦ by
    have hc : e ((LinearEquiv.symm e.toLinearEquiv) (ricciEnd r (e.toLinearEquiv u))) =
        ricciEnd r (e u) := e.toLinearEquiv.apply_symm_apply _
    rw [inner_ricciEnd_left, ricci_compContinuousLinearMap_linearIsometryEquiv]
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_symm, ← e.inner_map_map]
    rw [hc, inner_ricciEnd_left]

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
  ext m; rw [vec4_eta m, compContinuousLinearMap_apply_vec]
  simp [scalarPart_apply, scalar_compContinuousLinearMap_linearIsometryEquiv,
    e.toLinearEquiv.finrank_eq]

theorem tracelessRicciPart_compContinuousLinearMap_linearIsometryEquiv (e : W ≃ₗᵢ[ℝ] V)
    (r : FourTensor V) :
    tracelessRicciPart
        (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      (tracelessRicciPart r).compContinuousLinearMap fun _ ↦
        e.toLinearIsometry.toContinuousLinearMap := by
  ext m; rw [vec4_eta m, compContinuousLinearMap_apply_vec, tracelessRicciPart_apply,
    tracelessRicciPart_apply, smul_apply, smul_apply, e.toLinearEquiv.finrank_eq]
  congr 1
  simp only [kulkarniNomizu_apply, innerₗ_apply_apply,
    tracelessRicci_compContinuousLinearMap_linearIsometryEquiv,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    e.inner_map_map]

theorem schouten_compContinuousLinearMap_linearIsometryEquiv (e : W ≃ₗᵢ[ℝ] V)
    (r : FourTensor V) (u v : W) :
    schouten (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) u v =
      schouten r (e u) (e v) := by
  simp [schouten_apply, ricci_compContinuousLinearMap_linearIsometryEquiv,
    scalar_compContinuousLinearMap_linearIsometryEquiv, e.toLinearEquiv.finrank_eq]

theorem weyl_compContinuousLinearMap_linearIsometryEquiv (e : W ≃ₗᵢ[ℝ] V) (r : FourTensor V) :
    weyl (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      (weyl r).compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap := by
  ext m; simp [weyl_apply, scalarPart_compContinuousLinearMap_linearIsometryEquiv e r,
    tracelessRicciPart_compContinuousLinearMap_linearIsometryEquiv e r]

end Equivariance

/-! ### Contraction adjointness, pairwise orthogonality, and the Pythagorean identity -/

section Orthogonality

variable {ι : Type*} [Fintype ι]

omit [FiniteDimensional ℝ V] in
private theorem sum_inner_mul_apply (b : OrthonormalBasis ι ℝ V) (d : ι) (F : ι → ℝ) :
    (∑ e, ⟪b d, b e⟫ * F e) = F d := by
  classical simp [orthonormal_iff_ite.mp b.orthonormal]

omit [FiniteDimensional ℝ V] in
private theorem sum_smul_mul (c : ℝ) (f g : FourTensor V) (b : OrthonormalBasis ι ℝ V) :
    (∑ i, ∑ j, ∑ k, ∑ l, (c • f) ![b i, b j, b k, b l] * g ![b i, b j, b k, b l]) =
      c * ∑ i, ∑ j, ∑ k, ∑ l, f ![b i, b j, b k, b l] * g ![b i, b j, b k, b l] := by
  simp_rw [smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]

private theorem tracelessRicciPart_antisymm_first (r : FourTensor V) (u v z w : V) :
    tracelessRicciPart r ![u, v, z, w] = -tracelessRicciPart r ![v, u, z, w] := by
  rw [tracelessRicciPart_apply, smul_apply, smul_apply, kulkarniNomizu_antisymm_first, smul_neg]

private theorem tracelessRicciPart_antisymm_last (r : FourTensor V) (u v z w : V) :
    tracelessRicciPart r ![u, v, z, w] = -tracelessRicciPart r ![u, v, w, z] := by
  rw [tracelessRicciPart_apply, smul_apply, smul_apply, kulkarniNomizu_antisymm_last, smul_neg]

private theorem sum_kn_term₂ (b : OrthonormalBasis ι ℝ V) (h : BilinForm ℝ V)
    (q : FourTensor V) :
    (∑ i, ∑ j, ∑ k, ∑ l, h (b j) (b l) * ⟪b i, b k⟫ * q ![b i, b j, b k, b l]) =
      ∑ j, ∑ l, h (b j) (b l) * ricci q (b j) (b l) := by
  have hl (i j : ι) :
      (∑ k, ∑ l, h (b j) (b l) * ⟪b i, b k⟫ * q ![b i, b j, b k, b l]) =
        ∑ l, h (b j) (b l) * q ![b i, b j, b i, b l] := by
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun l _ ↦ ?_
    simp_rw [show ∀ k, h (b j) (b l) * ⟪b i, b k⟫ * q ![b i, b j, b k, b l] =
      ⟪b i, b k⟫ * (h (b j) (b l) * q ![b i, b j, b k, b l]) by intros; ring,
      sum_inner_mul_apply]
  simp_rw [hl, ricci_apply_orthonormalBasis b, Finset.mul_sum]
  rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm

private theorem sum_kn_term₃ (b : OrthonormalBasis ι ℝ V) (h : BilinForm ℝ V)
    {q : FourTensor V} (hq₁ : ∀ u v z w, q ![u, v, z, w] = -q ![v, u, z, w]) :
    (∑ i, ∑ j, ∑ k, ∑ l, h (b i) (b l) * ⟪b j, b k⟫ * q ![b i, b j, b k, b l]) =
      -∑ i, ∑ l, h (b i) (b l) * ricci q (b i) (b l) := by
  rw [Finset.sum_comm, ← sum_kn_term₂ b h q]; simp_rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦
    Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by rw [hq₁]; ring

private theorem sum_kn_term₄ (b : OrthonormalBasis ι ℝ V) (h : BilinForm ℝ V)
    {q : FourTensor V} (hq₂ : ∀ u v z w, q ![u, v, z, w] = -q ![u, v, w, z]) :
    (∑ i, ∑ j, ∑ k, ∑ l, h (b j) (b k) * ⟪b i, b l⟫ * q ![b i, b j, b k, b l]) =
      -∑ j, ∑ k, h (b j) (b k) * ricci q (b j) (b k) := by
  have hk (i j : ι) :
      (∑ k, ∑ l, h (b j) (b k) * ⟪b i, b l⟫ * q ![b i, b j, b k, b l]) =
        -∑ k, ∑ l, h (b j) (b l) * ⟪b i, b k⟫ * q ![b i, b j, b k, b l] := by
    rw [Finset.sum_comm]; simp_rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by rw [hq₂]; ring
  simp_rw [hk, Finset.sum_neg_distrib, sum_kn_term₂]

private theorem sum_kn_term₁ (b : OrthonormalBasis ι ℝ V) (h : BilinForm ℝ V)
    {q : FourTensor V} (hq₁₂ : ∀ u v z w, q ![u, v, z, w] = q ![v, u, w, z]) :
    (∑ i, ∑ j, ∑ k, ∑ l, h (b i) (b k) * ⟪b j, b l⟫ * q ![b i, b j, b k, b l]) =
      ∑ i, ∑ k, h (b i) (b k) * ricci q (b i) (b k) := by
  rw [Finset.sum_comm]
  have hk (j i : ι) :
      (∑ k, ∑ l, h (b i) (b k) * ⟪b j, b l⟫ * q ![b i, b j, b k, b l]) =
        ∑ k, ∑ l, h (b i) (b l) * ⟪b j, b k⟫ * q ![b j, b i, b k, b l] := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by rw [hq₁₂]
  simp_rw [hk, sum_kn_term₂]

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
    sum_kn_term₄ b h hq₂]; ring

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
    simp only [constantCurvature_apply, innerₗ_apply_apply]; ring
  simp_rw [hc, Finset.sum_sub_distrib]
  rw [sum_kn_term₂ b (innerₗ V) q, sum_kn_term₃ b (innerₗ V) hq₁]
  simp only [innerₗ_apply_apply, sum_inner_mul_apply, ← bilinFormTrace_eq_sum (ricci q) b,
    ← scalar_apply]; ring

theorem sum_constantCurvature_sq (b : OrthonormalBasis ι ℝ V) :
    (∑ i, ∑ j, ∑ k, ∑ l, constantCurvature V ![b i, b j, b k, b l] ^ 2) =
      2 * (Module.finrank ℝ V : ℝ) * ((Module.finrank ℝ V : ℝ) - 1) := by
  simp only [sq]
  rw [sum_constantCurvature_mul b isAlgebraicCurvature_constantCurvature.antisymm_first,
    scalar_constantCurvature, mul_assoc]

/-- The squared component norm of `scalarPart r` in any orthonormal basis is
`2 * scalar r ^ 2 / (n (n - 1))`. -/
theorem sum_scalarPart_sq (r : FourTensor V) (b : OrthonormalBasis ι ℝ V) :
    (∑ i, ∑ j, ∑ k, ∑ l, scalarPart r ![b i, b j, b k, b l] ^ 2) =
      2 * scalar r ^ 2 / ((Module.finrank ℝ V : ℝ) * ((Module.finrank ℝ V : ℝ) - 1)) := by
  rcases (by omega : Module.finrank ℝ V = 0 ∨ Module.finrank ℝ V = 1 ∨ 2 ≤ Module.finrank ℝ V)
    with h0 | h1 | hn
  · simp [scalarPart_apply, h0]
  · simp [scalarPart_apply, h1]
  · have : (Module.finrank ℝ V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have := finrank_sub_one_ne_zero (V := V) (by omega)
    have hsmul (c : ℝ) (f : FourTensor V) :
        (∑ i, ∑ j, ∑ k, ∑ l, (c • f) ![b i, b j, b k, b l] ^ 2) =
          c ^ 2 * ∑ i, ∑ j, ∑ k, ∑ l, f ![b i, b j, b k, b l] ^ 2 := by
      simp_rw [smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
    rw [scalarPart_apply, hsmul, sum_constantCurvature_sq b]; field_simp

/-- The squared component norm of `tracelessRicciPart r` in any orthonormal basis is
`(4 / (n - 2)) * ∑ i, ∑ k, tracelessRicci r (b i) (b k) ^ 2`. -/
theorem sum_tracelessRicciPart_sq (r : FourTensor V) (b : OrthonormalBasis ι ℝ V) :
    (∑ i, ∑ j, ∑ k, ∑ l, tracelessRicciPart r ![b i, b j, b k, b l] ^ 2) =
      (4 / ((Module.finrank ℝ V : ℝ) - 2)) *
        ∑ i, ∑ k, tracelessRicci r (b i) (b k) ^ 2 := by
  rcases eq_or_ne (Module.finrank ℝ V) 2 with hn2 | hn2
  · simp [tracelessRicciPart_apply, hn2]
  · simp_rw [sq]
    conv_lhs => enter [2, i, 2, j, 2, k, 2, l, 1]; rw [tracelessRicciPart_apply]
    rw [sum_smul_mul, sum_kulkarniNomizu_innerₗ_mul b (tracelessRicci r)
      (tracelessRicciPart_antisymm_first r) (tracelessRicciPart_antisymm_last r),
      ricci_tracelessRicciPart_of_ne_two hn2 r]; ring

/-- The scalar part of any four-tensor is orthogonal to the trace-free Ricci part of any
four-tensor. -/
theorem sum_scalarPart_mul_tracelessRicciPart (r q : FourTensor V)
    (b : OrthonormalBasis ι ℝ V) :
    (∑ i, ∑ j, ∑ k, ∑ l,
        scalarPart r ![b i, b j, b k, b l] *
          tracelessRicciPart q ![b i, b j, b k, b l]) = 0 := by
  rw [scalarPart_apply, sum_smul_mul, sum_constantCurvature_mul b
    (tracelessRicciPart_antisymm_first q), scalar_tracelessRicciPart, mul_zero, mul_zero]

/-- The scalar part of any four-tensor is orthogonal to the Weyl part of any algebraic curvature
tensor. -/
theorem IsAlgebraicCurvature.sum_scalarPart_mul_weyl (r : FourTensor V) {q : FourTensor V}
    (hq : IsAlgebraicCurvature q) (b : OrthonormalBasis ι ℝ V) :
    (∑ i, ∑ j, ∑ k, ∑ l,
        scalarPart r ![b i, b j, b k, b l] * FourTensor.weyl q ![b i, b j, b k, b l]) = 0 := by
  rw [scalarPart_apply, sum_smul_mul, sum_constantCurvature_mul b hq.weyl.antisymm_first,
    hq.scalar_weyl, mul_zero, mul_zero]

/-- The trace-free Ricci part of any four-tensor is orthogonal to the Weyl part of any algebraic
curvature tensor. -/
theorem IsAlgebraicCurvature.sum_tracelessRicciPart_mul_weyl (r : FourTensor V)
    {q : FourTensor V} (hq : IsAlgebraicCurvature q) (b : OrthonormalBasis ι ℝ V) :
    (∑ i, ∑ j, ∑ k, ∑ l,
        FourTensor.tracelessRicciPart r ![b i, b j, b k, b l] *
          FourTensor.weyl q ![b i, b j, b k, b l]) = 0 := by
  rw [tracelessRicciPart_apply, sum_smul_mul,
    hq.weyl.sum_kulkarniNomizu_innerₗ_mul b (tracelessRicci r), hq.ricci_weyl]; simp

/-- **Pythagorean decomposition of an algebraic curvature tensor**: in any orthonormal basis, the
squared component norm of `r` is the sum of the squared component norms of its scalar, trace-free
Ricci, and Weyl parts. -/
theorem IsAlgebraicCurvature.sum_sq_eq_add {r : FourTensor V} (hr : IsAlgebraicCurvature r)
    (b : OrthonormalBasis ι ℝ V) :
    (∑ i, ∑ j, ∑ k, ∑ l, r ![b i, b j, b k, b l] ^ 2) =
      (∑ i, ∑ j, ∑ k, ∑ l, scalarPart r ![b i, b j, b k, b l] ^ 2) +
        (∑ i, ∑ j, ∑ k, ∑ l, FourTensor.tracelessRicciPart r ![b i, b j, b k, b l] ^ 2) +
        (∑ i, ∑ j, ∑ k, ∑ l, FourTensor.weyl r ![b i, b j, b k, b l] ^ 2) := by
  have hmul2 (F : ι → ι → ι → ι → ℝ) :
      (∑ i, ∑ j, ∑ k, ∑ l, 2 * F i j k l) = 2 * ∑ i, ∑ j, ∑ k, ∑ l, F i j k l := by
    simp_rw [← Finset.mul_sum]
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
    simp only [add_apply]; ring
  simp only [hexp, Finset.sum_add_distrib, hmul2,
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
