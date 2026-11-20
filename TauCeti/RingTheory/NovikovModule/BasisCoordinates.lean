/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovModule.Grading
public import TauCeti.RingTheory.NovikovModule.Topology
public import TauCeti.RingTheory.NovikovSeries.Convolution
public import TauCeti.RingTheory.NovikovSeries.Grading
public import TauCeti.RingTheory.NovikovSeries.Map
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Novikov series with coefficients in a module, in the coordinates of a basis

Let `H` be an additive group with a period homomorphism `N : H →+ ℝ`, and let `V` be a module
over a ring `R`. A Novikov series with coefficients in `V`, an element of
`TauCeti.NovikovSeries V H N`, is a function `v : H → V`, `A ↦ v_A`, with finitely many nonzero
values on `{A | N A < C}` for every real `C`. They form an `R`-module, which models the completed
module `V ⊗̂ Λ` over the Novikov ring `Λ = NovikovSeries R H N`; no `Λ`-action is defined on it
here. Its `Λ`-module structure is the one moved over by the coordinate map `κ_b` below from
`TauCeti.NovikovModule.module`, and by `TauCeti.NovikovSeries.changeOfBasis` it does not depend
on the basis `b`. For `H = H₂(X; ℤ)` and the symplectic area `N = ω`, and
`V = H^*(X; ℚ)`, it is the state space on which quantum products and Gromov–Witten operations of
a closed symplectic manifold `X` take values, and its Cauchy product
`(v ⋆ w)_C = ∑_(A + A' = C) v_A ⊗ w_(A')` is the shape of every such product.

Tau Ceti develops completed modules over Novikov rings in coordinates, as the completed
combinations `TauCeti.NovikovModule R F` of generators with a potential `F`. This file identifies
the two descriptions. For a finite basis `b` of `V` indexed by `ι`, the generators are the pairs
`⟨i, A⟩` of `Σ i : ι, H` with potential `⟨i, A⟩ ↦ -N A` (`TauCeti.NovikovSeries.sigmaPotential`),
and the *coordinate map* `κ_b = TauCeti.NovikovSeries.toNovikovModule b` sends `v` to the
combination with coefficient `b^*_i (v_A)` at `⟨i, A⟩`. It is an `R`-linear bijection, and:

* it matches the filtrations: `v` vanishes below the period `C` exactly when `κ_b v` vanishes at
  the generators of potential `> -C`
  (`TauCeti.NovikovSeries.toNovikovModule_mem_potentialFiltration_iff`,
  `TauCeti.NovikovSeries.map_periodFiltration_toNovikovModule`);
* for a grading `𝒱` of `V` spanned by the basis vectors of each degree, and a degree `δ` on `H`,
  it matches the series of degree `D`, those with `v_A ∈ 𝒱 (D - δ A)` for every `A`
  (`TauCeti.NovikovSeries.gradeByCoeff`), with the completed combinations of degree `D` for the
  degree `⟨i, A⟩ ↦ deg i + δ A` (`TauCeti.NovikovSeries.toNovikovModule_mem_gradeBy_iff`). For
  `V = R` in degree `0` the series of degree `D` are the piece `TauCeti.NovikovSeries.gradeBy` of
  the Novikov ring (`TauCeti.NovikovSeries.gradeByCoeff_ite_eq_gradeBy`);
* it turns the Cauchy product, the convolution `TauCeti.NovikovSeries.convolution` along the
  tensor product `V → W → V ⊗ W`, into the kernel product
  `TauCeti.NovikovModule.kernelProduct`, in the tensor basis `b ⊗ b'`
  (`TauCeti.NovikovSeries.toNovikovModule_convolution_mk`). The kernel is
  `TauCeti.NovikovModule.kernelOfMatrix` of the constant structure matrix with entry `1` at
  `(i, j, (i, j))` and `0` elsewhere, relative to the lifts `⟨i, 0⟩`, so the existing API of
  kernels of matrices supplies its completed outputs, its translation invariance and its potential
  bound. These are the hypotheses of `TauCeti.NovikovModule.novikovKernelProduct`, which makes the
  kernel product Novikov-bilinear, and the potential bound and completed outputs are those of
  `TauCeti.NovikovModule.continuous_kernelProduct`, its joint continuity. The degree hypothesis
  of `TauCeti.NovikovModule.kernelProduct_mem_gradeBy` is not proved here for this kernel;
* for two bases `b` and `b₁`, the composite `κ_(b₁) ∘ κ_b⁻¹` is linear over the Novikov ring for
  the module structures `TauCeti.NovikovModule.module` of both sides
  (`TauCeti.NovikovSeries.changeOfBasis`), and its matrix in the Novikov bases of the lifts
  `⟨i, 0⟩` is the change-of-basis matrix from `b` to `b₁`, with constant entries
  (`TauCeti.NovikovSeries.toMatrix_changeOfBasis`). So the Novikov module structure transported
  to `V ⊗̂ Λ` by `κ_b` does not depend on the basis.

For `V = R` with the basis `1`, the coordinate of `κ_1 v` at the lift `⟨i, 0⟩` is `v` itself
(`TauCeti.NovikovSeries.coordinates_toNovikovModule_singleton`).

## Main definitions

* `TauCeti.NovikovSeries.sigmaPotential`: the potential `⟨i, A⟩ ↦ -N A` of the generators.
* `TauCeti.NovikovSeries.toNovikovModule`: the coordinate map `κ_b`, built from the coordinates
  `TauCeti.NovikovSeries.basisCoords` of `TauCeti.RingTheory.NovikovSeries.Map`.
* `TauCeti.NovikovSeries.changeOfBasis`: `κ_(b₁) ∘ κ_b⁻¹` as a Novikov-linear equivalence.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 11.1, on quantum cohomology with coefficients in the
  Novikov ring and its completed tensor products.
* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524.
-/

public section

noncomputable section

open Finset Function Set

namespace TauCeti

namespace NovikovSeries

variable {R : Type*}

section Coordinates

variable {H : Type*} [AddGroup H] {N : H →+ ℝ} {ι : Type*}

variable (N ι) in
/-- The potential `⟨i, A⟩ ↦ -N A` on the disjoint union of copies of `H` indexed by `ι`. Its
completed combinations are the basis coordinates of Novikov series with coefficients in a module
with a basis indexed by `ι`. -/
def sigmaPotential : (Σ _ : ι, H) → ℝ := fun p => -N p.2

/-- The potential of `⟨i, A⟩` is `-N A`. -/
@[simp]
theorem sigmaPotential_apply (p : Σ _ : ι, H) : sigmaPotential N ι p = -N p.2 :=
  (rfl)

/-- Translating a generator by `h` lowers the potential by the period of `h`: each copy of `H`
is a torsor under `H` with equivariant potential, as in `TauCeti.NovikovModule.coordinates`. -/
theorem sigmaPotential_vadd (i : ι) (h p : H) :
    sigmaPotential N ι ⟨i, h +ᵥ p⟩ = sigmaPotential N ι ⟨i, p⟩ - N h := by
  simp only [sigmaPotential_apply, vadd_eq_add, map_add]
  ring

variable [Semiring R] {V : Type*} [AddCommMonoid V] [Module R V] [Finite ι]

/-- **The coordinate map of a basis.** For a finite basis `b` of `V`, a Novikov series `v` with
coefficients in `V` is sent to the completed combination of the generators `⟨i, A⟩` of
`Σ i, H` whose coefficient at `⟨i, A⟩` is the `i`-th coordinate `b^*_i (v_A)` of the coefficient
of `v` at `A`. The potential is `⟨i, A⟩ ↦ -N A`, so the support condition of Novikov series
becomes the finiteness condition of completed combinations. -/
def toNovikovModule (b : Module.Basis ι R V) :
    NovikovSeries V H N ≃ₗ[R] NovikovModule R (sigmaPotential N ι) :=
  (basisCoords b).trans (NovikovModule.coordinates sigmaPotential_vadd 0).symm

/-- The coefficient of `κ_b v` at `⟨i, A⟩` is the `i`-th coordinate of `v_A`. -/
@[simp]
theorem toNovikovModule_apply_val (b : Module.Basis ι R V) (v : NovikovSeries V H N) (i : ι)
    (A : H) : (toNovikovModule b v).val ⟨i, A⟩ = b.repr (v.coeff A) i := by
  simp [toNovikovModule]

/-- The inverse of the coordinate map reassembles the coefficient at `A` from the coefficients
at the generators `⟨i, A⟩`. -/
@[simp]
theorem coeff_toNovikovModule_symm [Fintype ι] (b : Module.Basis ι R V)
    (a : NovikovModule R (sigmaPotential N ι)) (A : H) :
    ((toNovikovModule b).symm a).coeff A = ∑ i, a.val ⟨i, A⟩ • b i := by
  simp [toNovikovModule]

/-- In the coordinates of the lifts `⟨i, 0⟩` of `TauCeti.NovikovModule.coordinates`, the
coordinate map of `b` is the family of scalar Novikov series `A ↦ b^*_i (v_A)`. -/
@[simp]
theorem coordinates_toNovikovModule (b : Module.Basis ι R V) (v : NovikovSeries V H N) :
    NovikovModule.coordinates sigmaPotential_vadd 0 (toNovikovModule b v) = basisCoords b v := by
  simp [toNovikovModule]

/-- For `V = R` with the basis `1`, the coordinate at the lift `⟨i, 0⟩` of a Novikov series is the
series itself. -/
theorem coordinates_toNovikovModule_singleton [Unique ι] (v : NovikovSeries R H N) (i : ι) :
    NovikovModule.coordinates sigmaPotential_vadd 0
      (toNovikovModule (Module.Basis.singleton ι R) v) i = v := by
  ext A
  simp

end Coordinates

section Filtration

variable {H : Type*} [AddGroup H] {N : H →+ ℝ} {ι : Type*} [Finite ι] [Ring R] {V : Type*}
  [AddCommGroup V] [Module R V]

/-- **The coordinate map matches the filtrations.** A Novikov series with coefficients in `V`
vanishes below the period `C` exactly when its coordinates vanish at all generators of potential
`> -C`. -/
theorem toNovikovModule_mem_potentialFiltration_iff (b : Module.Basis ι R V)
    {v : NovikovSeries V H N} {C : ℝ} :
    toNovikovModule b v ∈ NovikovModule.potentialFiltration R (sigmaPotential N ι) (-C) ↔
      v ∈ periodFiltration V N C := by
  simp only [NovikovModule.mem_potentialFiltration, mem_periodFiltration, Sigma.forall,
    sigmaPotential_apply, neg_lt_neg_iff, toNovikovModule_apply_val]
  refine ⟨fun hv A hA => b.repr.injective ?_, fun hv i A hA => by simp [hv A hA]⟩
  ext i
  simpa using hv i A hA

/-- The coordinate map carries the period filtration of Novikov series with coefficients in `V`
onto the potential filtration of completed combinations. -/
theorem map_periodFiltration_toNovikovModule (b : Module.Basis ι R V) (C : ℝ) :
    (periodFiltration V N C).map (toNovikovModule b).toAddMonoidHom =
      NovikovModule.potentialFiltration R (sigmaPotential N ι) (-C) := by
  ext a
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (toNovikovModule_mem_potentialFiltration_iff b).2 hv
  · intro ha
    refine ⟨(toNovikovModule b).symm a, ?_, by simp⟩
    exact (toNovikovModule_mem_potentialFiltration_iff b).1 (by simpa using ha)

end Filtration

section Grading

variable {Γ : Type*} [AddCommGroup Γ]

variable {H : Type*} [AddGroup H] {N : H →+ ℝ} {ι : Type*} [Finite ι] [Semiring R] {V : Type*}
  [AddCommMonoid V] [Module R V]

/-- **The coordinate map matches the gradings.** Let `b` be a basis of `V` adapted to the
grading `𝒱`, in the sense that `𝒱 k` is spanned by the basis vectors of degree `k`. A Novikov
series with coefficients in `V` has degree `D` exactly when its coordinates are homogeneous of
degree `D` for the degree `⟨i, A⟩ ↦ deg i + δ A` of the generators. -/
theorem toNovikovModule_mem_gradeBy_iff (b : Module.Basis ι R V) {𝒱 : Γ → Submodule R V}
    {deg : ι → Γ} (h𝒱 : ∀ k, 𝒱 k = Submodule.span R (b '' (deg ⁻¹' {k}))) (δ : H → Γ)
    {D : Γ} {v : NovikovSeries V H N} :
    toNovikovModule b v ∈
        NovikovModule.gradeBy R (sigmaPotential N ι) (fun p => deg p.1 + δ p.2) D ↔
      v ∈ gradeByCoeff N 𝒱 δ D := by
  simp only [NovikovModule.mem_gradeBy_iff, Sigma.forall, toNovikovModule_apply_val,
    mem_gradeByCoeff, h𝒱, Module.Basis.mem_span_image]
  refine ⟨fun hv A i hi => ?_, fun hv i A hi => ?_⟩
  · simpa [eq_sub_iff_add_eq] using hv i A (by simpa using hi)
  · simpa [eq_sub_iff_add_eq] using hv A (by simpa using hi)

end Grading

section CauchyProduct

variable {H : Type*} [AddCommGroup H] {N : H →+ ℝ} {ι κ : Type*} [Finite ι] [Finite κ]
  [DecidableEq ι] [DecidableEq κ] [CommSemiring R] {V W : Type*} [AddCommMonoid V] [Module R V]
  [AddCommMonoid W] [Module R W] {C : ℝ}

/-- **The coordinate map turns the Cauchy product into the kernel product.** For bases `b` of `V`
and `b'` of `W`, the coordinates of the Cauchy product `(v ⋆ w)_A₀ = ∑_(A + A' = A₀) v_A ⊗ w_(A')`
in the basis `b ⊗ b'` of `V ⊗ W` are the product of the coordinates of `v` and `w` for the kernel
`TauCeti.NovikovModule.kernelOfMatrix` of the constant matrix with entry `1` at `(i, j, (i, j))`
and `0` elsewhere, relative to the lifts `⟨i, 0⟩`. The potential bound `hn` holds with `C = 0`
over a ring, by `TauCeti.NovikovModule.potential_le_of_kernelOfMatrix_ne_zero`, and for some `C`
in general, by `TauCeti.NovikovModule.exists_potential_le_of_kernelOfMatrix_ne_zero`. -/
theorem toNovikovModule_convolution_mk (b : Module.Basis ι R V) (b' : Module.Basis κ R W)
    (hn : ∀ p₁ p₂ p₀, NovikovModule.kernelOfMatrix (fun _ => (0 : H)) (fun _ => 0) (fun _ => 0)
        (fun i j k => if k = (i, j) then (1 : NovikovSeries R H N) else 0) p₁ p₂ p₀ ≠ 0 →
      sigmaPotential N (ι × κ) p₀ ≤ sigmaPotential N ι p₁ + sigmaPotential N κ p₂ + C)
    (v : NovikovSeries V H N) (w : NovikovSeries W H N) :
    toNovikovModule (b.tensorProduct b') (convolution (TensorProduct.mk R V W) v w) =
      NovikovModule.kernelProduct hn (NovikovModule.kernelOfMatrix_mem sigmaPotential_vadd _ _ _ _)
        (toNovikovModule b v) (toNovikovModule b' w) := by
  classical
  ext ⟨⟨i, j⟩, A₀⟩
  let T := (finite_setOf_add_eq v w A₀).toFinset
  have hT : ∀ p ∈ T, p.1 + p.2 = A₀ := fun p hp => ((Set.Finite.mem_toFinset _).1 hp).1
  let e : H × H ↪ (Σ _ : ι, H) × (Σ _ : κ, H) :=
    ⟨fun p => (⟨i, p.1⟩, ⟨j, p.2⟩), fun p p' hpp' => by
      simp only [Prod.mk.injEq, Sigma.mk.injEq, heq_eq_eq, true_and] at hpp'
      exact Prod.ext hpp'.1 hpp'.2⟩
  rw [NovikovModule.kernelProduct_apply_val_eq_sum _ _ _ _ _ (s := T.map e) fun q hq₁ hq₂ hn => ?_,
    toNovikovModule_apply_val, coeff_convolution, sum_map, map_sum, Finsupp.finsetSum_apply]
  · refine sum_congr rfl fun p hp => ?_
    have he : e p = (⟨i, p.1⟩, ⟨j, p.2⟩) := rfl
    have hA₀ : A₀ - p.1 - p.2 = 0 := by rw [← hT p hp]; abel
    simp only [he, TensorProduct.mk_apply, Module.Basis.tensorProduct_repr_tmul_apply,
      toNovikovModule_apply_val, NovikovModule.kernelOfMatrix_apply, vsub_eq_sub, sub_zero, hA₀,
      ite_true, coeff_one, mul_one, smul_eq_mul]
    exact mul_comm _ _
  · obtain ⟨⟨i', A⟩, ⟨j', A'⟩⟩ := q
    simp only [NovikovModule.kernelOfMatrix_apply, vsub_eq_sub, sub_zero] at hn
    split_ifs at hn with h₁
    · simp only [Prod.mk.injEq] at h₁
      obtain ⟨rfl, rfl⟩ := h₁
      simp only [toNovikovModule_apply_val] at hq₁ hq₂
      have h₂ : A₀ - A - A' = 0 := by
        by_contra h₂
        exact hn (by simp [h₂])
      refine Finset.mem_map.2 ⟨(A, A'), (Set.Finite.mem_toFinset _).2 ⟨?_, ?_, ?_⟩, rfl⟩
      · rw [sub_sub, sub_eq_zero] at h₂
        exact h₂.symm
      · exact fun h0 => hq₁ (by simp [h0])
      · exact fun h0 => hq₂ (by simp [h0])
    · exact absurd (coeff_zero _) hn

end CauchyProduct

section ChangeOfBasis

open Matrix

variable {H : Type*} [AddCommGroup H] {N : H →+ ℝ} {ι ι₁ : Type*} [Fintype ι] [Finite ι₁]
  [CommSemiring R] {V : Type*} [AddCommMonoid V] [Module R V]

/-- **Change of basis in coordinates.** For two bases `b` and `b₁` of `V`, the composite
`κ_(b₁) ∘ κ_b⁻¹` of the coordinate maps acts on the coordinates at the lifts `⟨i, 0⟩` by the
change-of-basis matrix from `b` to `b₁`, with constant entries. -/
theorem coordinates_toNovikovModule_toNovikovModule_symm (b : Module.Basis ι R V)
    (b₁ : Module.Basis ι₁ R V) (a : NovikovModule R (sigmaPotential N ι)) :
    NovikovModule.coordinates sigmaPotential_vadd 0
        (toNovikovModule b₁ ((toNovikovModule b).symm a)) =
      (b₁.toMatrix b).map (algebraMap R (NovikovSeries R H N)) *ᵥ
        NovikovModule.coordinates sigmaPotential_vadd 0 a := by
  ext j A
  simp [coeff_toNovikovModule_symm, Matrix.mulVec, dotProduct, coeff_sum, algebraMap_apply,
    Module.Basis.toMatrix_apply, mul_comm]

/-- **Change of basis is Novikov-linear.** For two bases `b` and `b₁` of `V`, the composite
`κ_(b₁) ∘ κ_b⁻¹` of the coordinate maps is a linear equivalence over the Novikov ring, for the
Novikov module structures `TauCeti.NovikovModule.module` of both sides. -/
def changeOfBasis (b : Module.Basis ι R V) (b₁ : Module.Basis ι₁ R V) :
    letI := NovikovModule.module (R := R) (sigmaPotential_vadd (N := N) (ι := ι))
    letI := NovikovModule.module (R := R) (sigmaPotential_vadd (N := N) (ι := ι₁))
    NovikovModule R (sigmaPotential N ι) ≃ₗ[NovikovSeries R H N]
      NovikovModule R (sigmaPotential N ι₁) :=
  letI := NovikovModule.module (R := R) (sigmaPotential_vadd (N := N) (ι := ι))
  letI := NovikovModule.module (R := R) (sigmaPotential_vadd (N := N) (ι := ι₁))
  { (toNovikovModule b).symm.trans (toNovikovModule b₁) with
    map_smul' c a := by
      apply (NovikovModule.coordinates sigmaPotential_vadd 0).injective
      simp [-coordinates_toNovikovModule, coordinates_toNovikovModule_toNovikovModule_symm,
        NovikovModule.coordinates_smul, Matrix.mulVec_smul] }

/-- The change of basis is the composite `κ_(b₁) ∘ κ_b⁻¹` of the coordinate maps. -/
@[simp]
theorem changeOfBasis_apply (b : Module.Basis ι R V) (b₁ : Module.Basis ι₁ R V)
    (a : NovikovModule R (sigmaPotential N ι)) :
    letI := NovikovModule.module (R := R) (sigmaPotential_vadd (N := N) (ι := ι))
    letI := NovikovModule.module (R := R) (sigmaPotential_vadd (N := N) (ι := ι₁))
    changeOfBasis (N := N) b b₁ a = toNovikovModule b₁ ((toNovikovModule b).symm a) :=
  (rfl)

/-- The matrix of the change of basis `κ_(b₁) ∘ κ_b⁻¹` in the Novikov bases of the lifts
`⟨i, 0⟩` is the change-of-basis matrix from `b` to `b₁`, with constant entries. -/
theorem toMatrix_changeOfBasis [DecidableEq ι] (b : Module.Basis ι R V)
    (b₁ : Module.Basis ι₁ R V) :
    letI := NovikovModule.module (R := R) (sigmaPotential_vadd (N := N) (ι := ι))
    letI := NovikovModule.module (R := R) (sigmaPotential_vadd (N := N) (ι := ι₁))
    LinearMap.toMatrix (NovikovModule.basis sigmaPotential_vadd 0)
        (NovikovModule.basis sigmaPotential_vadd 0) (changeOfBasis (N := N) b b₁).toLinearMap =
      (b₁.toMatrix b).map (algebraMap R (NovikovSeries R H N)) := by
  let := NovikovModule.module (R := R) (sigmaPotential_vadd (N := N) (ι := ι))
  let := NovikovModule.module (R := R) (sigmaPotential_vadd (N := N) (ι := ι₁))
  refine Matrix.ext fun j i => ?_
  simp [-coordinates_toNovikovModule, LinearMap.toMatrix_apply, NovikovModule.basis_repr_apply,
    coordinates_toNovikovModule_toNovikovModule_symm, NovikovModule.coordinates_basis]

end ChangeOfBasis

end NovikovSeries

end TauCeti
