/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovModule.Grading
public import TauCeti.RingTheory.NovikovModule.Topology
public import TauCeti.RingTheory.NovikovSeries.Map
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Novikov series with coefficients in a module, in the coordinates of a basis

Let `H` be an additive group with a period homomorphism `N : H →+ ℝ`, and let `V` be a module
over a ring `R`. A Novikov series with coefficients in `V`, an element of
`TauCeti.NovikovSeries V H N`, is a function `v : H → V`, `A ↦ v_A`, with finitely many nonzero
values on `{A | N A < C}` for every real `C`. These form the completed module `V ⊗̂ Λ` over the
Novikov ring `Λ = NovikovSeries R H N`. For `H = H₂(X; ℤ)` and the symplectic area `N = ω`, and
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
  `TauCeti.NovikovModule.kernelProduct` of the kernel `TauCeti.NovikovSeries.cauchyKernel`, in
  the tensor basis `b ⊗ b'` (`TauCeti.NovikovSeries.toNovikovModule_convolution_mk`). The kernel
  has potential bound `0` and is invariant under translating an input and the output together, so
  the bilinear theory of `TauCeti.RingTheory.NovikovModule.Bilinear` (Novikov-bilinearity,
  continuity, gradings) applies to it;
* for two bases `b` and `b₁`, the composite `κ_(b₁) ∘ κ_b⁻¹` is linear over the Novikov ring for
  the module structures `TauCeti.NovikovModule.module` of both sides
  (`TauCeti.NovikovSeries.changeOfBasis`), and its matrix in the Novikov bases of the lifts
  `⟨i, 0⟩` is the change-of-basis matrix from `b` to `b₁`, with constant entries
  (`TauCeti.NovikovSeries.toMatrix_changeOfBasis`). So the Novikov module structure transported
  to `V ⊗̂ Λ` by `κ_b` does not depend on the basis.

For `V = R` with the basis `1`, the coordinate of `κ_1 v` at the lift `⟨i, 0⟩` is `v` itself
(`TauCeti.NovikovSeries.coordinates_toNovikovModule_singleton`).

## Main definitions

* `TauCeti.NovikovSeries.congrLinearEquiv`, `TauCeti.NovikovSeries.piLinearEquiv`,
  `TauCeti.NovikovSeries.basisCoords`: coefficientwise linear equivalences, and the coordinates of
  a Novikov series with coefficients in `V` as a family of scalar Novikov series.
* `TauCeti.NovikovSeries.toNovikovModule`: the coordinate map `κ_b`.
* `TauCeti.NovikovSeries.gradeByCoeff`: the series of a given degree.
* `TauCeti.NovikovSeries.convolution`: the convolution of Novikov series along a bilinear map.
* `TauCeti.NovikovSeries.cauchyKernel`: the kernel of the Cauchy product in basis coordinates.
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

section Equiv

variable {H : Type*} [AddZeroClass H] {N : H →+ ℝ} [Semiring R] {V W : Type*} [AddCommMonoid V]
  [Module R V] [AddCommMonoid W] [Module R W]

/-- A linear equivalence of coefficients, applied coefficientwise to Novikov series: the
pushforward `TauCeti.NovikovSeries.map` along `e` and the identity of exponents, which is linear
for the ground-ring actions. -/
def congrLinearEquiv (e : V ≃ₗ[R] W) : NovikovSeries V H N ≃ₗ[R] NovikovSeries W H N where
  toFun := NovikovSeries.map e.toAddEquiv.toAddMonoidHom (AddMonoidHom.id H)
    exists_period_rescale_id
  invFun := NovikovSeries.map e.symm.toAddEquiv.toAddMonoidHom (AddMonoidHom.id H)
    exists_period_rescale_id
  left_inv v := by ext h; simp
  right_inv w := by ext h; simp
  map_add' := map_add _
  map_smul' c v := by ext h; simp

/-- The coefficients of `congrLinearEquiv e v` are the images under `e` of those of `v`. -/
@[simp]
theorem coeff_congrLinearEquiv (e : V ≃ₗ[R] W) (v : NovikovSeries V H N) (h : H) :
    (congrLinearEquiv e v).coeff h = e (v.coeff h) := by
  simp [congrLinearEquiv]

/-- The coefficients of `(congrLinearEquiv e).symm w` are the images under `e.symm` of those of
`w`. -/
@[simp]
theorem coeff_congrLinearEquiv_symm (e : V ≃ₗ[R] W) (w : NovikovSeries W H N) (h : H) :
    ((congrLinearEquiv e).symm w).coeff h = e.symm (w.coeff h) := by
  simp [congrLinearEquiv]

variable {ι : Type*} [Finite ι] {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

variable (R) in
/-- Novikov series with coefficients in a finite product are families of Novikov series. -/
def piLinearEquiv : NovikovSeries (∀ i, M i) H N ≃ₗ[R] (∀ i, NovikovSeries (M i) H N) where
  toFun v i :=
    { coeff h := v.coeff h i
      finite_lt C := (v.finite_lt C).subset fun h hh =>
        ⟨fun hv => hh.1 (by rw [hv, Pi.zero_apply]), hh.2⟩ }
  invFun v :=
    { coeff h i := (v i).coeff h
      finite_lt C := (Set.finite_iUnion fun i => (v i).finite_lt C).subset fun h hh => by
        obtain ⟨i, hi⟩ := Function.ne_iff.1 hh.1
        exact Set.mem_iUnion.2 ⟨i, hi, hh.2⟩ }
  left_inv v := by ext h i; rfl
  right_inv v := by ext i h; rfl
  map_add' v w := by ext i h; rfl
  map_smul' c v := by ext i h; rfl

/-- The `i`-th series of `piLinearEquiv R v` has the `i`-th components of the coefficients of
`v`. -/
@[simp]
theorem coeff_piLinearEquiv_apply (v : NovikovSeries (∀ i, M i) H N) (i : ι) (h : H) :
    (piLinearEquiv R v i).coeff h = v.coeff h i :=
  (rfl)

/-- The coefficients of `(piLinearEquiv R).symm v` collect the coefficients of the series
`v i`. -/
@[simp]
theorem coeff_piLinearEquiv_symm_apply (v : ∀ i, NovikovSeries (M i) H N) (h : H) (i : ι) :
    ((piLinearEquiv R).symm v).coeff h i = (v i).coeff h :=
  (rfl)

/-- The coordinates of a Novikov series with coefficients in a module with a finite basis: one
Novikov series with scalar coefficients for each basis vector. -/
def basisCoords (b : Module.Basis ι R V) :
    NovikovSeries V H N ≃ₗ[R] (ι → NovikovSeries R H N) :=
  (congrLinearEquiv b.equivFun).trans (piLinearEquiv R)

/-- The `i`-th coordinate series has the `i`-th basis coordinates of the coefficients. -/
@[simp]
theorem coeff_basisCoords (b : Module.Basis ι R V) (v : NovikovSeries V H N) (i : ι) (h : H) :
    (basisCoords b v i).coeff h = b.repr (v.coeff h) i := by
  simp [basisCoords]

/-- A family of scalar series is the coordinates of the series with coefficients
`∑ i, (v i)_h • b i`. -/
theorem coeff_basisCoords_symm [Fintype ι] (b : Module.Basis ι R V)
    (v : ι → NovikovSeries R H N) (h : H) :
    ((basisCoords b).symm v).coeff h = ∑ i, (v i).coeff h • b i := by
  simp [basisCoords, Module.Basis.equivFun_symm_apply]

end Equiv

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
theorem coeff_toNovikovModule_symm [Fintype ι] (b : Module.Basis ι R V)
    (a : NovikovModule R (sigmaPotential N ι)) (A : H) :
    ((toNovikovModule b).symm a).coeff A = ∑ i, a.val ⟨i, A⟩ • b i := by
  simp [toNovikovModule, coeff_basisCoords_symm]

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

section Def

variable {H : Type*} [AddZeroClass H] {N : H →+ ℝ} [Semiring R] {V : Type*} [AddCommMonoid V]
  [Module R V]

variable (N) in
/-- The Novikov series of degree `D` with coefficients in a graded module: for a grading `𝒱` of
`V` and a degree `δ A` of the exponents, those `v` with `v_A ∈ 𝒱 (D - δ A)` for every `A`. For
`V = R` concentrated in degree `0` these are the series supported on `δ⁻¹ {D}`
(`TauCeti.NovikovSeries.gradeByCoeff_ite_eq_gradeBy`). -/
def gradeByCoeff (𝒱 : Γ → Submodule R V) (δ : H → Γ) (D : Γ) :
    Submodule R (NovikovSeries V H N) where
  carrier := {v | ∀ A, v.coeff A ∈ 𝒱 (D - δ A)}
  zero_mem' A := by simp
  add_mem' hv hw A := by simpa using add_mem (hv A) (hw A)
  smul_mem' c v hv A := by simpa using Submodule.smul_mem _ c (hv A)

/-- A series has degree `D` exactly when each coefficient `v_A` has degree `D - δ A`. -/
@[simp]
theorem mem_gradeByCoeff {𝒱 : Γ → Submodule R V} {δ : H → Γ} {D : Γ}
    {v : NovikovSeries V H N} : v ∈ gradeByCoeff N 𝒱 δ D ↔ ∀ A, v.coeff A ∈ 𝒱 (D - δ A) :=
  Iff.rfl

/-- For `R` itself concentrated in degree `0`, the series of degree `D` are those supported on
the exponents of degree `D`, the pieces `TauCeti.NovikovSeries.gradeBy` of the Novikov ring. -/
theorem gradeByCoeff_ite_eq_gradeBy [DecidableEq Γ] (δ : H → Γ) (D : Γ) :
    gradeByCoeff N (fun k => if k = 0 then ⊤ else ⊥ : Γ → Submodule R R) δ D =
      gradeBy R N δ D := by
  ext v
  simp only [mem_gradeByCoeff, mem_gradeBy_iff, Set.subset_def, mem_support, Set.mem_preimage,
    Set.mem_singleton_iff, sub_eq_zero]
  refine forall_congr' fun A => ?_
  by_cases hA : D = δ A
  · simp [hA]
  · simp [hA, Ne.symm hA]

end Def

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

section Convolution

variable {H : Type*} [AddZeroClass H] {N : H →+ ℝ} [CommSemiring R] {V W U : Type*}
  [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W] [AddCommMonoid U] [Module R U]
  (β : V →ₗ[R] W →ₗ[R] U)

/-- The convolution of two Novikov series with coefficients in `V` and `W` along a bilinear map
`β`, before bundling: the coefficient at `h` is the finite sum of `β (v_u) (w_u')` over the pairs
of support exponents with `u + u' = h`. -/
private def convolve (v : NovikovSeries V H N) (w : NovikovSeries W H N) :
    NovikovSeries U H N where
  coeff h := ∑ p ∈ (finite_setOf_add_eq v w h).toFinset, β (v.coeff p.1) (w.coeff p.2)
  finite_lt C := ((finite_setOf_period_add_lt v w C).image fun p => p.1 + p.2).subset <| by
    rintro h ⟨hh, hC⟩
    obtain ⟨p, hp, -⟩ := exists_ne_zero_of_sum_ne_zero hh
    rw [Set.Finite.mem_toFinset] at hp
    exact ⟨p, ⟨by rw [hp.1]; exact hC, hp.2⟩, hp.1⟩

/-- A coefficient of the convolution is the sum over any finite set of pairs adding up to the
exponent that contains every pair of support exponents. -/
private theorem coeff_convolve_eq_sum {v : NovikovSeries V H N} {w : NovikovSeries W H N} {h : H}
    {s : Finset (H × H)} (hs : ∀ p ∈ s, p.1 + p.2 = h)
    (hvw : ∀ u u', u + u' = h → v.coeff u ≠ 0 → w.coeff u' ≠ 0 → (u, u') ∈ s) :
    (convolve β v w).coeff h = ∑ p ∈ s, β (v.coeff p.1) (w.coeff p.2) := by
  refine sum_subset (fun p hp => ?_) fun p hps hp => ?_
  · rw [Set.Finite.mem_toFinset] at hp
    exact hvw p.1 p.2 hp.1 hp.2.1 hp.2.2
  · rw [Set.Finite.mem_toFinset] at hp
    by_cases hv : v.coeff p.1 = 0
    · rw [hv, map_zero, LinearMap.zero_apply]
    by_cases hw : w.coeff p.2 = 0
    · rw [hw, map_zero]
    exact absurd ⟨hs p hps, hv, hw⟩ hp

/-- The pairs of support exponents of `v` and `w` adding up to `h`, as a finite set. -/
private abbrev supportPairs (v : NovikovSeries V H N) (w : NovikovSeries W H N) (h : H) :
    Finset (H × H) :=
  (finite_setOf_add_eq v w h).toFinset

private theorem mem_supportPairs {v : NovikovSeries V H N} {w : NovikovSeries W H N} {h : H}
    {u u' : H} : (u, u') ∈ supportPairs v w h ↔ u + u' = h ∧ v.coeff u ≠ 0 ∧ w.coeff u' ≠ 0 :=
  Set.Finite.mem_toFinset _

private theorem add_eq_of_mem_supportPairs {v : NovikovSeries V H N} {w : NovikovSeries W H N}
    {h : H} {p : H × H} (hp : p ∈ supportPairs v w h) : p.1 + p.2 = h :=
  ((Set.Finite.mem_toFinset _).1 hp).1

private theorem convolve_add_left (v v' : NovikovSeries V H N) (w : NovikovSeries W H N) :
    convolve β (v + v') w = convolve β v w + convolve β v' w := by
  classical
  ext h
  have hs : ∀ p ∈ supportPairs v w h ∪ supportPairs v' w h, p.1 + p.2 = h := fun p hp => by
    rcases Finset.mem_union.1 hp with hp | hp <;> exact add_eq_of_mem_supportPairs hp
  have h₁ := coeff_convolve_eq_sum β (v := v) (w := w) hs fun u u' huu' hv hw =>
    Finset.mem_union_left _ (mem_supportPairs.2 ⟨huu', hv, hw⟩)
  have h₂ := coeff_convolve_eq_sum β (v := v') (w := w) hs fun u u' huu' hv hw =>
    Finset.mem_union_right _ (mem_supportPairs.2 ⟨huu', hv, hw⟩)
  have h₀ := coeff_convolve_eq_sum β (v := v + v') (w := w) hs fun u u' huu' hv hw => by
    rw [coeff_add] at hv
    by_cases hv' : v.coeff u = 0
    · exact Finset.mem_union_right _ (mem_supportPairs.2 ⟨huu', by simpa [hv'] using hv, hw⟩)
    · exact Finset.mem_union_left _ (mem_supportPairs.2 ⟨huu', hv', hw⟩)
  rw [coeff_add, h₀, h₁, h₂, ← sum_add_distrib]
  simp only [coeff_add, map_add, LinearMap.add_apply]

private theorem convolve_add_right (v : NovikovSeries V H N) (w w' : NovikovSeries W H N) :
    convolve β v (w + w') = convolve β v w + convolve β v w' := by
  classical
  ext h
  have hs : ∀ p ∈ supportPairs v w h ∪ supportPairs v w' h, p.1 + p.2 = h := fun p hp => by
    rcases Finset.mem_union.1 hp with hp | hp <;> exact add_eq_of_mem_supportPairs hp
  have h₁ := coeff_convolve_eq_sum β (v := v) (w := w) hs fun u u' huu' hv hw =>
    Finset.mem_union_left _ (mem_supportPairs.2 ⟨huu', hv, hw⟩)
  have h₂ := coeff_convolve_eq_sum β (v := v) (w := w') hs fun u u' huu' hv hw =>
    Finset.mem_union_right _ (mem_supportPairs.2 ⟨huu', hv, hw⟩)
  have h₀ := coeff_convolve_eq_sum β (v := v) (w := w + w') hs fun u u' huu' hv hw => by
    rw [coeff_add] at hw
    by_cases hw' : w.coeff u' = 0
    · exact Finset.mem_union_right _ (mem_supportPairs.2 ⟨huu', hv, by simpa [hw'] using hw⟩)
    · exact Finset.mem_union_left _ (mem_supportPairs.2 ⟨huu', hv, hw'⟩)
  rw [coeff_add, h₀, h₁, h₂, ← sum_add_distrib]
  simp only [coeff_add, map_add]

private theorem convolve_smul_left (c : R) (v : NovikovSeries V H N) (w : NovikovSeries W H N) :
    convolve β (c • v) w = c • convolve β v w := by
  ext h
  have hs : ∀ p ∈ supportPairs v w h, p.1 + p.2 = h := fun p hp => add_eq_of_mem_supportPairs hp
  have h₁ := coeff_convolve_eq_sum β (v := v) (w := w) hs fun u u' huu' hv hw =>
    mem_supportPairs.2 ⟨huu', hv, hw⟩
  have h₀ := coeff_convolve_eq_sum β (v := c • v) (w := w) hs fun u u' huu' hv hw =>
    mem_supportPairs.2 ⟨huu', fun h0 => hv (by rw [coeff_smul, h0, smul_zero]), hw⟩
  rw [coeff_smul, h₀, h₁, smul_sum]
  simp only [coeff_smul, map_smul, LinearMap.smul_apply]

private theorem convolve_smul_right (c : R) (v : NovikovSeries V H N) (w : NovikovSeries W H N) :
    convolve β v (c • w) = c • convolve β v w := by
  ext h
  have hs : ∀ p ∈ supportPairs v w h, p.1 + p.2 = h := fun p hp => add_eq_of_mem_supportPairs hp
  have h₁ := coeff_convolve_eq_sum β (v := v) (w := w) hs fun u u' huu' hv hw =>
    mem_supportPairs.2 ⟨huu', hv, hw⟩
  have h₀ := coeff_convolve_eq_sum β (v := v) (w := c • w) hs fun u u' huu' hv hw =>
    mem_supportPairs.2 ⟨huu', hv, fun h0 => hw (by rw [coeff_smul, h0, smul_zero])⟩
  rw [coeff_smul, h₀, h₁, smul_sum]
  simp only [coeff_smul, map_smul]

/-- **The convolution of Novikov series along a bilinear map.** For an `R`-bilinear map
`β : V → W → U`, the coefficient of `convolution β v w` at `h` is `∑_(u + u' = h) β (v_u) (w_u')`,
a finite sum. For `β` the multiplication of `R` this is the product of Novikov series, and for
the tensor product `V → W → V ⊗ W` it is the Cauchy product of Novikov series with coefficients in
`V` and `W`. -/
def convolution :
    NovikovSeries V H N →ₗ[R] NovikovSeries W H N →ₗ[R] NovikovSeries U H N :=
  LinearMap.mk₂ R (convolve β) (convolve_add_left β) (convolve_smul_left β)
    (convolve_add_right β) (convolve_smul_right β)

/-- A coefficient of the convolution is the sum of `β (v_u) (w_u')` over the finite set of pairs
of support exponents with `u + u' = h`. -/
theorem coeff_convolution (v : NovikovSeries V H N) (w : NovikovSeries W H N) (h : H) :
    (convolution β v w).coeff h =
      ∑ p ∈ (finite_setOf_add_eq v w h).toFinset, β (v.coeff p.1) (w.coeff p.2) :=
  (rfl)

/-- A coefficient of the convolution may be computed over any finite set of pairs adding up to
the exponent that contains every pair of support exponents. -/
theorem coeff_convolution_eq_sum {v : NovikovSeries V H N} {w : NovikovSeries W H N} {h : H}
    {s : Finset (H × H)} (hs : ∀ p ∈ s, p.1 + p.2 = h)
    (hvw : ∀ u u', u + u' = h → v.coeff u ≠ 0 → w.coeff u' ≠ 0 → (u, u') ∈ s) :
    (convolution β v w).coeff h = ∑ p ∈ s, β (v.coeff p.1) (w.coeff p.2) :=
  coeff_convolve_eq_sum β hs hvw

/-- Convolving monomials adds their exponents. -/
@[simp]
theorem convolution_single_single (g g' : H) (x : V) (y : W) :
    convolution β (single g x : NovikovSeries V H N) (single g' y) = single (g + g') (β x y) := by
  classical
  ext h
  by_cases hh : g + g' = h
  · rw [coeff_convolution_eq_sum β (s := {(g, g')}) (by simpa using hh) fun u u' _ hu hu' => ?_,
      sum_singleton, coeff_single_same, coeff_single_same, ← hh, coeff_single_same]
    rw [Finset.mem_singleton, Prod.mk.injEq]
    exact ⟨by_contra fun hug => hu (coeff_single_of_ne hug x),
      by_contra fun hug => hu' (coeff_single_of_ne hug y)⟩
  · rw [coeff_convolution_eq_sum β (s := ∅) (by simp) fun u u' huu' hu hu' => ?_, sum_empty,
      coeff_single_of_ne (Ne.symm hh)]
    have hu : u = g := by_contra fun hug => hu (coeff_single_of_ne hug x)
    have hu' : u' = g' := by_contra fun hug => hu' (coeff_single_of_ne hug y)
    exact absurd (hu ▸ hu' ▸ huu') hh

/-- Convolution along the multiplication of `R` is the product of Novikov series. -/
theorem convolution_mul (a b : NovikovSeries R H N) :
    convolution (LinearMap.mul R R) a b = a * b := by
  ext h
  simp [coeff_convolution, coeff_mul]

end Convolution

section CauchyProduct

variable {H : Type*} [AddGroup H] {N : H →+ ℝ} {ι κ : Type*} [CommSemiring R]

variable (R H ι κ) in
open scoped Classical in
/-- The kernel of the Cauchy product in basis coordinates: the coefficient at the inputs
`⟨i, A⟩`, `⟨j, A'⟩` and the output `⟨(k, l), C⟩` is `1` when `(k, l) = (i, j)` and `C = A + A'`,
and `0` otherwise. -/
def cauchyKernel (p : Σ _ : ι, H) (q : Σ _ : κ, H) (r : Σ _ : ι × κ, H) : R :=
  if r.1 = (p.1, q.1) ∧ r.2 = p.2 + q.2 then 1 else 0

/-- The Cauchy kernel for any decidability instance of its defining condition. -/
theorem cauchyKernel_apply (p : Σ _ : ι, H) (q : Σ _ : κ, H) (r : Σ _ : ι × κ, H)
    [Decidable (r.1 = (p.1, q.1) ∧ r.2 = p.2 + q.2)] :
    cauchyKernel R H ι κ p q r = if r.1 = (p.1, q.1) ∧ r.2 = p.2 + q.2 then 1 else 0 := by
  simp only [cauchyKernel]
  congr

/-- A nonzero coefficient of the Cauchy kernel sits at the output generator
`⟨(i, j), A + A'⟩` of the inputs `⟨i, A⟩` and `⟨j, A'⟩`. -/
theorem eq_and_eq_of_cauchyKernel_ne_zero {p : Σ _ : ι, H} {q : Σ _ : κ, H}
    {r : Σ _ : ι × κ, H} (h : cauchyKernel R H ι κ p q r ≠ 0) :
    r.1 = (p.1, q.1) ∧ r.2 = p.2 + q.2 := by
  classical
  rw [cauchyKernel_apply] at h
  by_contra hr
  exact h (by simp [hr])

/-- The Cauchy kernel has potential bound `0`: the output potential is the sum of the input
potentials. -/
theorem sigmaPotential_le_of_cauchyKernel_ne_zero (p : Σ _ : ι, H) (q : Σ _ : κ, H)
    (r : Σ _ : ι × κ, H) (h : cauchyKernel R H ι κ p q r ≠ 0) :
    sigmaPotential N (ι × κ) r ≤ sigmaPotential N ι p + sigmaPotential N κ q + 0 := by
  simp [(eq_and_eq_of_cauchyKernel_ne_zero h).2, add_comm]

/-- Each pair of inputs has a single output generator. -/
theorem cauchyKernel_mem (p : Σ _ : ι, H) (q : Σ _ : κ, H) :
    cauchyKernel R H ι κ p q ∈ NovikovModule R (sigmaPotential N (ι × κ)) :=
  NovikovModule.mem_of_finite_support <| (Set.finite_singleton
    (⟨(p.1, q.1), p.2 + q.2⟩ : Σ _ : ι × κ, H)).subset fun r hr => by
      obtain ⟨h₁, h₂⟩ := eq_and_eq_of_cauchyKernel_ne_zero hr
      exact Sigma.ext h₁ (heq_of_eq h₂)

/-- The Cauchy kernel is unchanged when the first input and the output are translated by the
same class. -/
theorem cauchyKernel_vadd_left (g : H) (i : ι) (p₁ : H) (p₂ : Σ _ : κ, H) (k : ι × κ)
    (p₀ : H) :
    cauchyKernel R H ι κ ⟨i, g +ᵥ p₁⟩ p₂ ⟨k, g +ᵥ p₀⟩ =
      cauchyKernel R H ι κ ⟨i, p₁⟩ p₂ ⟨k, p₀⟩ := by
  classical
  simp only [cauchyKernel_apply, vadd_eq_add, add_assoc, add_right_inj]

variable [Finite ι] [Finite κ] {V W : Type*} [AddCommMonoid V] [Module R V] [AddCommMonoid W]
  [Module R W]

/-- **The coordinate map turns the Cauchy product into the kernel product.** For bases `b` of `V`
and `b'` of `W`, the coordinates of the Cauchy product `(v ⋆ w)_C = ∑_(A + A' = C) v_A ⊗ w_(A')`
in the basis `b ⊗ b'` of `V ⊗ W` are the product of the coordinates of `v` and `w` for the Cauchy
kernel. -/
theorem toNovikovModule_convolution_mk (b : Module.Basis ι R V) (b' : Module.Basis κ R W)
    (v : NovikovSeries V H N) (w : NovikovSeries W H N) :
    toNovikovModule (b.tensorProduct b') (convolution (TensorProduct.mk R V W) v w) =
      NovikovModule.kernelProduct sigmaPotential_le_of_cauchyKernel_ne_zero cauchyKernel_mem
        (toNovikovModule b v) (toNovikovModule b' w) := by
  classical
  ext ⟨⟨i, j⟩, C⟩
  let T := (finite_setOf_add_eq v w C).toFinset
  have hT : ∀ p ∈ T, p.1 + p.2 = C := fun p hp => ((Set.Finite.mem_toFinset _).1 hp).1
  let e : H × H ↪ (Σ _ : ι, H) × (Σ _ : κ, H) :=
    ⟨fun p => (⟨i, p.1⟩, ⟨j, p.2⟩), fun p p' hpp' => by
      simp only [Prod.mk.injEq, Sigma.mk.injEq, heq_eq_eq, true_and] at hpp'
      exact Prod.ext hpp'.1 hpp'.2⟩
  rw [NovikovModule.kernelProduct_apply_val_eq_sum _ _ _ _ _ (s := T.map e) fun q hq₁ hq₂ hn => ?_,
    toNovikovModule_apply_val, coeff_convolution, sum_map, map_sum, Finsupp.finsetSum_apply]
  · refine sum_congr rfl fun p hp => ?_
    have he : e p = (⟨i, p.1⟩, ⟨j, p.2⟩) := rfl
    simp only [he, TensorProduct.mk_apply, Module.Basis.tensorProduct_repr_tmul_apply,
      toNovikovModule_apply_val, cauchyKernel_apply, hT p hp, and_self, ite_true, mul_one,
      smul_eq_mul]
    exact mul_comm _ _
  · obtain ⟨⟨i', A⟩, ⟨j', A'⟩⟩ := q
    obtain ⟨h₁, h₂⟩ := eq_and_eq_of_cauchyKernel_ne_zero hn
    simp only [Prod.mk.injEq] at h₁
    obtain ⟨rfl, rfl⟩ := h₁
    simp only [toNovikovModule_apply_val] at hq₁ hq₂
    refine Finset.mem_map.2 ⟨(A, A'), (Set.Finite.mem_toFinset _).2 ⟨h₂.symm, ?_, ?_⟩, rfl⟩
    · exact fun h0 => hq₁ (by simp [h0])
    · exact fun h0 => hq₂ (by simp [h0])

end CauchyProduct

section CauchyKernel

variable {H : Type*} [AddCommGroup H] {ι κ : Type*} [CommSemiring R]

/-- The Cauchy kernel is unchanged when the second input and the output are translated by the
same class. -/
theorem cauchyKernel_vadd_right (g : H) (p₁ : Σ _ : ι, H) (j : κ) (p₂ : H) (k : ι × κ)
    (p₀ : H) :
    cauchyKernel R H ι κ p₁ ⟨j, g +ᵥ p₂⟩ ⟨k, g +ᵥ p₀⟩ =
      cauchyKernel R H ι κ p₁ ⟨j, p₂⟩ ⟨k, p₀⟩ := by
  classical
  simp only [cauchyKernel_apply, vadd_eq_add, add_left_comm p₁.2 g p₂, add_right_inj]

end CauchyKernel

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
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
        LinearEquiv.trans_apply, RingHom.id_apply]
      rw [NovikovModule.coordinates_smul, coordinates_toNovikovModule_toNovikovModule_symm,
        coordinates_toNovikovModule_toNovikovModule_symm, NovikovModule.coordinates_smul,
        Matrix.mulVec_smul] }

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
  rw [LinearMap.toMatrix_apply, NovikovModule.basis_repr_apply, LinearEquiv.coe_coe,
    changeOfBasis_apply, coordinates_toNovikovModule_toNovikovModule_symm,
    NovikovModule.coordinates_basis, Matrix.mulVec_single_one]
  rfl

end ChangeOfBasis

end NovikovSeries

end TauCeti
