/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovModule.Grading
public import TauCeti.RingTheory.NovikovModule.Topology
public import TauCeti.RingTheory.NovikovSeries.BaseChange
public import TauCeti.RingTheory.NovikovSeries.Map
public import TauCeti.RingTheory.NovikovSeries.TensorProduct
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Vector-valued Novikov series in the coordinates of a basis

Let `H` be a commutative group with a period homomorphism `N : H →+ ℝ`, and let `V` be a module
over a commutative semiring `R`. A Novikov series with coefficients in `V`, an element of
`NovikovSeries V H N`, is a function `A ↦ v_A` from `H` to `V` with only finitely many nonzero
values on `{A | N A < C}` for every real `C`. For the second homology `H = H₂(X; ℤ)` of a closed
symplectic manifold with its area homomorphism, and `V = H^*(X; ℚ)`, this is the completed state
module `V ⊗̂ Λ_ω` of Gromov–Witten theory, on which the quantum product is defined; its scalar
case `V = R` is the Novikov ring `Λ_ω` itself.

This file identifies such series with Tau Ceti's completed combinations on generators. A finite
basis `b` of `V` indexed by `ι` gives the generators `⟨i, A⟩` of `Σ _ : ι, H`, with the potential
`⟨i, A⟩ ↦ -N A` (`TauCeti.NovikovSeries.negPeriod`), and the *basis coordinates*

`κ_b(v)⟨i, A⟩ = b^*_i(v_A)`,

with `b^*_i` the `i`-th coordinate function of `b`. This is an `R`-linear equivalence onto
`TauCeti.NovikovModule` (`TauCeti.NovikovSeries.basisCoordinates`). Through it the general
results on completed combinations apply to vector-valued series:

* **Filtration.** `v` vanishes on `{A | N A < C}` exactly when `κ_b(v)` lies in the
  potential filtration at level `-C`
  (`TauCeti.NovikovSeries.basisCoordinates_mem_potentialFiltration_iff`), so `κ_b` carries the
  period filtration onto the potential filtration
  (`TauCeti.NovikovSeries.map_periodFiltration_basisCoordinates`).
* **Grading.** If `V` is graded by submodules `𝒱 k` spanned by the basis vectors of degree `k`,
  and `H` carries a degree `δ` (twice the first Chern number in Gromov–Witten theory), then
  `κ_b(v)` is homogeneous of degree `k` for the degree `⟨i, A⟩ ↦ deg i + δ A` exactly when `v` lies
  in `TauCeti.NovikovSeries.gradeByCoeff`, that is `v_A ∈ 𝒱 (k - δ A)` for every `A`
  (`TauCeti.NovikovSeries.basisCoordinates_mem_gradeBy_iff`). For `V = R` in degree `0` these
  are the pieces `TauCeti.NovikovSeries.gradeBy` of the Novikov ring
  (`TauCeti.NovikovSeries.gradeByCoeff_ite_eq_gradeBy`).
* **Change of basis.** For a second basis `c`, the map `κ_c ∘ κ_b⁻¹` is the Novikov-linear map
  `TauCeti.NovikovModule.novikovMapOfMatrix` of the constant change-of-basis matrix `c^*_j(b_i)`
  relative to the lifts `⟨i, 0⟩` and `⟨j, 0⟩`
  (`TauCeti.NovikovSeries.basisCoordinates_basisCoordinates_symm_eq_novikovMapOfMatrix`). So it
  is linear for the Novikov module structures `TauCeti.NovikovModule.module` of both sides
  (`TauCeti.NovikovSeries.changeOfBasis`), and its matrix in the Novikov bases of the lifts is
  the change-of-basis matrix `c.toMatrix b` with constant entries
  (`TauCeti.NovikovSeries.toMatrix_changeOfBasis`): the Novikov module structure transported
  along `κ_b` does not depend on `b`.
* **Linearity over the Novikov ring.** The Novikov ring acts on vector-valued series by
  convolution (`TauCeti.NovikovSeries.module`, from `TauCeti.RingTheory.NovikovSeries.BaseChange`),
  and `κ_b` is linear for this action and `TauCeti.NovikovModule.module`
  (`TauCeti.NovikovSeries.basisCoordinates_smul`). It sends the basis of constant series
  `single 0 (b i)` to the basis of the lifts `⟨i, 0⟩`
  (`TauCeti.NovikovSeries.basisCoordinates_basis`), the image of the basis `1 ⊗ b i` of the base
  change of `V` to the Novikov ring under the canonical isomorphism
  `TauCeti.NovikovSeries.ofTensorProductEquiv`.
* **The Cauchy product.** The Cauchy product of series with coefficients in `V` and `W`
  (`TauCeti.NovikovSeries.cauchyProduct`, from `TauCeti.RingTheory.NovikovSeries.TensorProduct`)
  takes values in series with coefficients in `V ⊗[R] W`. In the coordinates of the bases
  `b`, `c` and `b ⊗ c` it is the kernel product (`TauCeti.NovikovModule.kernelProduct`) of the
  kernel `TauCeti.NovikovSeries.cauchyKernel`, which sends a pair of generators `⟨i, A⟩`,
  `⟨j, A'⟩` to the generator `⟨(i, j), A + A'⟩`
  (`TauCeti.NovikovSeries.basisCoordinates_cauchyProduct`). This kernel has potential bound `0`.
  For a commutative group `H`, it is the kernel `TauCeti.NovikovModule.kernelOfMatrix` of the
  constant matrix with entry `1` at `((i, j), i, j)` relative to the lifts `⟨i, 0⟩`
  (`TauCeti.NovikovSeries.cauchyKernel_eq_kernelOfMatrix`), so in coordinates the Cauchy product
  is the Novikov-bilinear map `TauCeti.NovikovModule.novikovProductOfMatrix` of this matrix
  (`TauCeti.NovikovSeries.basisCoordinates_cauchyProduct_eq_novikovProductOfMatrix`).

In the lifts `⟨i, 0⟩`, the coordinates of `κ_b(v)` are the family of scalar Novikov series
`TauCeti.NovikovSeries.basisCoords b v` of `TauCeti.RingTheory.NovikovSeries.Map`
(`TauCeti.NovikovSeries.coordinates_basisCoordinates`). For `V = R` with the basis `{1}`, the
coordinate of `κ(v)` at the lift `⟨i, 0⟩` is `v` itself
(`TauCeti.NovikovSeries.coordinates_basisCoordinates_singleton`).

## Main definitions

* `TauCeti.NovikovSeries.negPeriod ι N`: the potential `⟨i, A⟩ ↦ -N A` on `ι` copies of `H`.
* `TauCeti.NovikovSeries.basisCoordinates b`: the basis coordinates of a vector-valued Novikov
  series.
* `TauCeti.NovikovSeries.cauchyKernel`: the product kernel of the Cauchy product on basis
  coordinates.
* `TauCeti.NovikovSeries.changeOfBasis`: `κ_c ∘ κ_b⁻¹` as a Novikov-linear equivalence.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section 11.1 (the Novikov ring and quantum cohomology
  with Novikov coefficients).
* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524.
* M. Kontsevich and Yu. Manin, *Gromov–Witten classes, quantum cohomology, and enumerative
  geometry*, Comm. Math. Phys. 164 (1994), 525–562.
-/

public section

noncomputable section

open Function Set

open scoped TensorProduct

namespace TauCeti

namespace NovikovSeries

section Potential

variable {H : Type*} [AddZeroClass H] (ι : Type*) (N : H →+ ℝ)

/-- The potential `⟨i, A⟩ ↦ -N A` on `ι` copies of `H`. A completed combination for this
potential has only finitely many nonzero coefficients on `{⟨i, A⟩ | N A < C}` for every `C`. -/
def negPeriod (s : Σ _ : ι, H) : ℝ :=
  -N s.2

variable {ι N}

@[simp]
theorem negPeriod_apply (s : Σ _ : ι, H) : negPeriod ι N s = -N s.2 :=
  (rfl)

end Potential

section AddZeroClass

variable {R V W H ι κ : Type*} [AddZeroClass H] {N : H →+ ℝ}

section Coordinates

variable [Semiring R] [AddCommMonoid V] [Module R V]

/-- The basis coordinates of a vector-valued Novikov series are a completed combination. -/
private theorem repr_coeff_mem_novikovModule [Finite ι] (b : Module.Basis ι R V)
    (v : NovikovSeries V H N) :
    (fun s : Σ _ : ι, H => b.repr (v.coeff s.2) s.1) ∈ NovikovModule R (negPeriod ι N) := by
  refine NovikovModule.mem_iff.2 fun C => ?_
  refine (Set.finite_iUnion fun i : ι => (v.finite_lt (-C)).image (Sigma.mk i)).subset ?_
  rintro ⟨i, A⟩ ⟨hs, hC⟩
  refine Set.mem_iUnion.2 ⟨i, A, ⟨fun hv => hs ?_, ?_⟩, rfl⟩
  · simp [hv]
  · simp only [negPeriod_apply] at hC
    linarith

variable [Fintype ι] (b : Module.Basis ι R V)

/-- The vector-valued series with basis coordinates given by a completed combination is a Novikov
series. -/
private theorem sum_smul_mem_finite_lt (a : NovikovModule R (negPeriod ι N)) (C : ℝ) :
    {A : H | ∑ i, a.val ⟨i, A⟩ • b i ≠ 0 ∧ N A < C}.Finite := by
  refine (Set.finite_iUnion fun i : ι =>
    (NovikovModule.finite_gt a (-C)).preimage (sigma_mk_injective (i := i)).injOn).subset ?_
  rintro A ⟨hA, hC⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hA
  refine Set.mem_iUnion.2 ⟨i, fun h => hi (by simp [h]), ?_⟩
  simp only [negPeriod_apply]
  linarith

/-- **The basis coordinates of vector-valued Novikov series.** For a finite basis `b` of `V`, the
`R`-linear equivalence `κ_b` between Novikov series with coefficients in `V` and completed
combinations of the generators `⟨i, A⟩` for the potential `-N A`, with
`κ_b(v)⟨i, A⟩ = b.repr (v_A) i`. -/
def basisCoordinates :
    NovikovSeries V H N ≃ₗ[R] NovikovModule R (negPeriod ι N) where
  toFun v := ⟨fun s => b.repr (v.coeff s.2) s.1, repr_coeff_mem_novikovModule b v⟩
  invFun a := ⟨fun A => ∑ i, a.val ⟨i, A⟩ • b i, sum_smul_mem_finite_lt b a⟩
  map_add' v w := by
    ext s
    simp
  map_smul' r v := by
    ext s
    simp
  left_inv v := by
    ext A
    simp [b.sum_repr]
  right_inv a := by
    ext ⟨i, A⟩
    exact congrFun (b.repr_sum_self fun j => a.val ⟨j, A⟩) i

/-- The coefficient of a generator `⟨i, A⟩` in the basis coordinates is the `i`-th coordinate of
the coefficient at `A`. -/
@[simp]
theorem basisCoordinates_apply_val (v : NovikovSeries V H N) (s : Σ _ : ι, H) :
    (basisCoordinates b v).val s = b.repr (v.coeff s.2) s.1 :=
  (rfl)

/-- A vector-valued series is recovered from its basis coordinates. -/
@[simp]
theorem coeff_basisCoordinates_symm (a : NovikovModule R (negPeriod ι N)) (A : H) :
    ((basisCoordinates b).symm a).coeff A = ∑ i, a.val ⟨i, A⟩ • b i :=
  (rfl)

section Grading

variable {D : Type*} [AddGroup D] (deg : ι → D) (δ : H → D)

/-- **The grading in basis coordinates.** Let `V` be graded by submodules `𝒱 k`, each spanned by
the basis vectors of degree `k`, and give the generator `⟨i, A⟩` the degree `deg i + δ A`. Then
the basis coordinates of `v` are homogeneous of degree `k` exactly when `v` has degree `k`, that is
`v_A ∈ 𝒱 (k - δ A)` for every exponent `A`. -/
theorem basisCoordinates_mem_gradeBy_iff {𝒱 : D → Submodule R V}
    (h𝒱 : ∀ k, 𝒱 k = Submodule.span R (b '' {i | deg i = k})) {k : D}
    {v : NovikovSeries V H N} :
    basisCoordinates b v ∈
        NovikovModule.gradeBy R (negPeriod ι N) (fun s => deg s.1 + δ s.2) k ↔
      v ∈ gradeByCoeff N 𝒱 δ k := by
  simp only [NovikovModule.mem_gradeBy_iff, basisCoordinates_apply_val, Sigma.forall, h𝒱,
    Module.Basis.mem_span_image, mem_gradeByCoeff]
  refine ⟨fun h A i hi => eq_sub_of_add_eq (h i A (Finsupp.mem_support_iff.1 hi)),
    fun h i A hi => by rw [h A (Finsupp.mem_support_iff.2 hi), sub_add_cancel]⟩

end Grading

end Coordinates

section Filtration

variable [Ring R] [AddCommGroup V] [Module R V] [Fintype ι] (b : Module.Basis ι R V)

/-- **The filtration in basis coordinates.** A vector-valued series vanishes at every exponent of
period `< C` exactly when its basis coordinates lie in the potential filtration at level `-C`. -/
theorem basisCoordinates_mem_potentialFiltration_iff {C : ℝ} {v : NovikovSeries V H N} :
    basisCoordinates b v ∈ NovikovModule.potentialFiltration R (negPeriod ι N) (-C) ↔
      v ∈ periodFiltration V N C := by
  simp only [NovikovModule.mem_potentialFiltration, mem_periodFiltration,
    basisCoordinates_apply_val, negPeriod_apply, Sigma.forall, neg_lt_neg_iff]
  refine ⟨fun h A hA => b.repr.injective ?_, fun h i A hA => by simp [h A hA]⟩
  ext i
  simpa using h i A hA

/-- The basis coordinates carry the period filtration of vector-valued series onto the potential
filtration of completed combinations. -/
theorem map_periodFiltration_basisCoordinates (C : ℝ) :
    (periodFiltration V N C).map (basisCoordinates b).toAddMonoidHom =
      NovikovModule.potentialFiltration R (negPeriod ι N) (-C) := by
  ext a
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (basisCoordinates_mem_potentialFiltration_iff b).2 hv
  · intro ha
    refine ⟨(basisCoordinates b).symm a, ?_, by simp⟩
    exact (basisCoordinates_mem_potentialFiltration_iff b).1 (by simpa using ha)

end Filtration

section Kernel

variable [Semiring R]

open scoped Classical in
/-- **The Cauchy kernel** on basis coordinates: the pair of generators `⟨i, A⟩` and `⟨j, A'⟩`
goes to the generator `⟨(i, j), A + A'⟩` with coefficient `1`. -/
def cauchyKernel (p₁ : Σ _ : ι, H) (p₂ : Σ _ : κ, H) : (Σ _ : ι × κ, H) → R :=
  Pi.single ⟨(p₁.1, p₂.1), p₁.2 + p₂.2⟩ 1

/-- The Cauchy kernel is `1` at the generator `⟨(i, j), A + A'⟩` and `0` elsewhere. -/
theorem cauchyKernel_apply [DecidableEq (Σ _ : ι × κ, H)] (p₁ : Σ _ : ι, H) (p₂ : Σ _ : κ, H)
    (p₀ : Σ _ : ι × κ, H) :
    cauchyKernel (R := R) p₁ p₂ p₀ = if p₀ = ⟨(p₁.1, p₂.1), p₁.2 + p₂.2⟩ then 1 else 0 := by
  simp only [cauchyKernel, Pi.single_apply]
  -- Only the decidability instances differ: `cauchyKernel` uses the classical one.
  convert rfl

/-- The Cauchy kernel is `1` at the generator `⟨(i, j), A + A'⟩`. -/
@[simp]
theorem cauchyKernel_self (p₁ : Σ _ : ι, H) (p₂ : Σ _ : κ, H) :
    cauchyKernel (R := R) p₁ p₂ ⟨(p₁.1, p₂.1), p₁.2 + p₂.2⟩ = 1 := by
  simp [cauchyKernel]

/-- The Cauchy kernel vanishes at every generator other than `⟨(i, j), A + A'⟩`. -/
theorem cauchyKernel_of_ne {p₁ : Σ _ : ι, H} {p₂ : Σ _ : κ, H} {p₀ : Σ _ : ι × κ, H}
    (hp : p₀ ≠ ⟨(p₁.1, p₂.1), p₁.2 + p₂.2⟩) : cauchyKernel (R := R) p₁ p₂ p₀ = 0 := by
  classical
  simp [cauchyKernel_apply, hp]

/-- The Cauchy kernel has potential bound `0`: its output generator has exactly the sum of the
potentials of the input generators. -/
theorem potential_le_of_cauchyKernel_ne_zero (p₁ : Σ _ : ι, H) (p₂ : Σ _ : κ, H)
    (p₀ : Σ _ : ι × κ, H) (hp : cauchyKernel (R := R) p₁ p₂ p₀ ≠ 0) :
    negPeriod (ι × κ) N p₀ ≤ negPeriod ι N p₁ + negPeriod κ N p₂ + 0 := by
  obtain rfl := not_imp_comm.1 cauchyKernel_of_ne hp
  simp only [negPeriod_apply, map_add]
  linarith

/-- Each output of the Cauchy kernel is a single generator, hence a completed combination. -/
theorem cauchyKernel_mem (p₁ : Σ _ : ι, H) (p₂ : Σ _ : κ, H) :
    cauchyKernel (R := R) p₁ p₂ ∈ NovikovModule R (negPeriod (ι × κ) N) := by
  classical
  exact NovikovModule.pi_single_mem _ _

end Kernel

/-- **The Cauchy product in basis coordinates** is the kernel product of the Cauchy kernel: for
bases `b` of `V` and `c` of `W`, the coordinates of `v ⋆ w` in the basis `b ⊗ c` are the kernel
product of the coordinates of `v` in `b` and of `w` in `c`. -/
theorem basisCoordinates_cauchyProduct [CommSemiring R] [AddCommMonoid V] [Module R V]
    [AddCommMonoid W] [Module R W] [Fintype ι] [Fintype κ] (b : Module.Basis ι R V)
    (c : Module.Basis κ R W) (v : NovikovSeries V H N) (w : NovikovSeries W H N) :
    basisCoordinates (b.tensorProduct c) (cauchyProduct R v w) =
      NovikovModule.kernelProduct potential_le_of_cauchyKernel_ne_zero cauchyKernel_mem
        (basisCoordinates b v) (basisCoordinates c w) := by
  classical
  ext ⟨⟨i, j⟩, h⟩
  -- Both sides are sums over the generator pairs `(⟨i, u⟩, ⟨j, u'⟩)` with `(u, u')` a pair of
  -- support exponents adding up to `h`.
  let S := (finite_setOf_add_eq v w h).toFinset.image
    fun p => ((⟨i, p.1⟩ : Σ _ : ι, H), (⟨j, p.2⟩ : Σ _ : κ, H))
  have hS {q} (hq : q ∈ S) : q = (⟨i, q.1.2⟩, ⟨j, q.2.2⟩) ∧ q.1.2 + q.2.2 = h := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
    exact ⟨rfl, ((Set.Finite.mem_toFinset _).1 hp).1⟩
  rw [NovikovModule.kernelProduct_apply_val_eq_sum (s := S) (hs := ?_), basisCoordinates_apply_val,
    coeff_cauchyProduct_eq_sum_of_injOn (F := S) (f := fun q => (q.1.2, q.2.2))
      (fun q hq => (hS hq).2) ?_ ?_, map_sum, Finset.sum_apply']
  · refine Finset.sum_congr rfl fun q hq => ?_
    rw [(hS hq).1]
    simp [cauchyKernel_apply, (hS hq).2, mul_comm]
  · exact fun u u' huu' hu hu' => ⟨(⟨i, u⟩, ⟨j, u'⟩),
      Finset.mem_image.2 ⟨(u, u'), (Set.Finite.mem_toFinset _).2 ⟨huu', hu, hu'⟩, rfl⟩, rfl⟩
  · intro q hq q' hq' hqq'
    rw [(hS hq).1, (hS hq').1]
    exact congrArg (fun p : H × H => ((⟨i, p.1⟩ : Σ _ : ι, H), (⟨j, p.2⟩ : Σ _ : κ, H))) hqq'
  · rintro ⟨⟨i₁, u⟩, ⟨j₁, u'⟩⟩ hv hw hn
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ : ((i, j) = (i₁, j₁)) ∧ h = u + u' := by
      simpa using not_imp_comm.1 cauchyKernel_of_ne hn
    exact Finset.mem_image.2 ⟨(u, u'), (Set.Finite.mem_toFinset _).2
      ⟨rfl, fun h0 => hv (by simp [h0]), fun h0 => hw (by simp [h0])⟩, rfl⟩

end AddZeroClass

section AddGroup

variable {R V H ι κ : Type*} [AddGroup H] {N : H →+ ℝ}

/-- Translating a generator by `h` lowers its potential by the period of `h`: the equivariance
hypothesis of the coordinates `TauCeti.NovikovModule.coordinates`. -/
theorem negPeriod_vadd (i : ι) (h p : H) :
    negPeriod ι N ⟨i, h +ᵥ p⟩ = negPeriod ι N ⟨i, p⟩ - N h := by
  simp only [negPeriod_apply, vadd_eq_add, map_add]
  ring

section Lifts

variable [Semiring R] [AddCommMonoid V] [Module R V] [Fintype ι] (b : Module.Basis ι R V)

/-- In the lifts `⟨i, 0⟩`, the `i`-th Novikov coordinate of `κ_b(v)` is the series of the `i`-th
basis coordinates of the coefficients of `v`. -/
theorem coeff_coordinates_basisCoordinates (v : NovikovSeries V H N) (i : ι) (A : H) :
    (NovikovModule.coordinates negPeriod_vadd (fun _ => 0) (basisCoordinates b v) i).coeff A =
      b.repr (v.coeff A) i := by
  simp

/-- In the lifts `⟨i, 0⟩`, the Novikov coordinates of `κ_b(v)` are the family
`TauCeti.NovikovSeries.basisCoords b v` of scalar Novikov series `A ↦ b^*_i(v_A)`. -/
theorem coordinates_basisCoordinates (v : NovikovSeries V H N) :
    NovikovModule.coordinates negPeriod_vadd (fun _ => 0) (basisCoordinates b v) =
      basisCoords b v := by
  ext i A
  simp

/-- **The basis coordinates are linear over the Novikov ring**, for the convolution action
`TauCeti.NovikovSeries.module` on vector-valued series and the Novikov module structure
`TauCeti.NovikovModule.module` on completed combinations. So the Novikov module structure
transported along `κ_b` is the convolution action, for every basis `b`. -/
theorem basisCoordinates_smul (a : NovikovSeries R H N) (v : NovikovSeries V H N) :
    letI := module R V N
    letI := NovikovModule.module (R := R) (negPeriod_vadd (ι := ι) (N := N))
    basisCoordinates b (a • v) = a • basisCoordinates b v := by
  let := module R V N
  let := NovikovModule.module (R := R) (negPeriod_vadd (ι := ι) (N := N))
  apply (NovikovModule.coordinates negPeriod_vadd (fun _ => 0)).injective
  rw [NovikovModule.coordinates_smul, coordinates_basisCoordinates, coordinates_basisCoordinates,
    basisCoords_smul]

/-- The basis coordinates `κ_b` send the basis of constant series `single 0 (b i)` over the Novikov
ring to the basis `TauCeti.NovikovModule.basis` of the lifts `⟨i, 0⟩`. -/
theorem basisCoordinates_basis (i : ι) :
    letI := module R V N
    basisCoordinates b (basis (N := N) b i) =
      NovikovModule.basis negPeriod_vadd (fun _ => 0) i := by
  classical
  let := module R V N
  apply (NovikovModule.coordinates negPeriod_vadd (fun _ => 0)).injective
  rw [NovikovModule.coordinates_basis, coordinates_basisCoordinates]
  ext j : 1
  rw [← basis_repr_apply, Module.Basis.repr_self, Finsupp.single_apply, Pi.single_apply]
  simp [eq_comm]

/-- **The scalar case.** For `V = R` with the basis `{1}`, the coordinate of `κ(v)` at the lift
`⟨i, 0⟩` is the series `v` itself. -/
theorem coordinates_basisCoordinates_singleton {ι : Type*} [Unique ι] (v : NovikovSeries R H N)
    (i : ι) :
    NovikovModule.coordinates negPeriod_vadd (fun _ => 0)
      (basisCoordinates (Module.Basis.singleton ι R) v) i = v := by
  ext A
  simp

end Lifts

end AddGroup

section ChangeOfBasis

open Matrix

variable {R V H ι κ : Type*} [AddCommGroup H] {N : H →+ ℝ} [CommSemiring R] [AddCommMonoid V]
  [Module R V] [Fintype ι] [Fintype κ] (b : Module.Basis ι R V) (c : Module.Basis κ R V)

/-- **Change of basis.** `κ_c ∘ κ_b⁻¹` is the Novikov-linear map
`TauCeti.NovikovModule.novikovMapOfMatrix` of the constant change-of-basis matrix with entries
`c.repr (b i) j`, relative to the lifts `⟨i, 0⟩` and `⟨j, 0⟩`. So the Novikov module structure
transported to vector-valued series along `κ_b` does not depend on the basis `b`. -/
theorem basisCoordinates_basisCoordinates_symm_eq_novikovMapOfMatrix
    (a : NovikovModule R (negPeriod ι N)) :
    basisCoordinates c ((basisCoordinates b).symm a) =
      NovikovModule.novikovMapOfMatrix negPeriod_vadd negPeriod_vadd (fun _ => 0) (fun _ => 0)
        (Matrix.of fun i j => algebraMap R (NovikovSeries R H N) (c.repr (b i) j)) a := by
  apply (NovikovModule.coordinates (R := R) negPeriod_vadd (fun _ : κ => (0 : H))).injective
  ext1 j
  rw [NovikovModule.coordinates_novikovMapOfMatrix]
  ext A
  simp [coeff_sum, coeff_mul_single]

/-- **Change of basis in coordinates.** In the lifts `⟨i, 0⟩` and `⟨j, 0⟩`, the map `κ_c ∘ κ_b⁻¹`
acts on Novikov coordinates by the change-of-basis matrix `c.toMatrix b`, with constant
entries. -/
theorem coordinates_basisCoordinates_basisCoordinates_symm
    (a : NovikovModule R (negPeriod ι N)) :
    NovikovModule.coordinates negPeriod_vadd (fun _ => 0)
        (basisCoordinates c ((basisCoordinates b).symm a)) =
      (c.toMatrix b).map (algebraMap R (NovikovSeries R H N)) *ᵥ
        NovikovModule.coordinates negPeriod_vadd (fun _ => 0) a := by
  ext j A
  simp [Matrix.mulVec, dotProduct, coeff_sum, algebraMap_apply, Module.Basis.toMatrix_apply,
    mul_comm]

/-- **Change of basis is Novikov-linear.** For two bases `b` and `c` of `V`, the composite
`κ_c ∘ κ_b⁻¹` of the basis coordinates is a linear equivalence over the Novikov ring, for the
Novikov module structures `TauCeti.NovikovModule.module` of both sides. -/
def changeOfBasis :
    letI := NovikovModule.module (R := R) (negPeriod_vadd (N := N) (ι := ι))
    letI := NovikovModule.module (R := R) (negPeriod_vadd (N := N) (ι := κ))
    NovikovModule R (negPeriod ι N) ≃ₗ[NovikovSeries R H N] NovikovModule R (negPeriod κ N) :=
  letI := NovikovModule.module (R := R) (negPeriod_vadd (N := N) (ι := ι))
  letI := NovikovModule.module (R := R) (negPeriod_vadd (N := N) (ι := κ))
  { (basisCoordinates b).symm.trans (basisCoordinates c) with
    map_smul' r a := by
      apply (NovikovModule.coordinates negPeriod_vadd (fun _ => 0)).injective
      simp [coordinates_basisCoordinates_basisCoordinates_symm, NovikovModule.coordinates_smul,
        Matrix.mulVec_smul] }

/-- The change of basis is the composite `κ_c ∘ κ_b⁻¹` of the basis coordinates. -/
@[simp]
theorem changeOfBasis_apply (a : NovikovModule R (negPeriod ι N)) :
    letI := NovikovModule.module (R := R) (negPeriod_vadd (N := N) (ι := ι))
    letI := NovikovModule.module (R := R) (negPeriod_vadd (N := N) (ι := κ))
    changeOfBasis (N := N) b c a = basisCoordinates c ((basisCoordinates b).symm a) :=
  (rfl)

/-- The matrix of the change of basis `κ_c ∘ κ_b⁻¹` in the Novikov bases of the lifts `⟨i, 0⟩`
and `⟨j, 0⟩` is the change-of-basis matrix `c.toMatrix b`, with constant entries. -/
theorem toMatrix_changeOfBasis [DecidableEq ι] :
    letI := NovikovModule.module (R := R) (negPeriod_vadd (N := N) (ι := ι))
    letI := NovikovModule.module (R := R) (negPeriod_vadd (N := N) (ι := κ))
    LinearMap.toMatrix (NovikovModule.basis negPeriod_vadd (fun _ => 0))
        (NovikovModule.basis negPeriod_vadd (fun _ => 0)) (changeOfBasis (N := N) b c).toLinearMap =
      (c.toMatrix b).map (algebraMap R (NovikovSeries R H N)) := by
  let := NovikovModule.module (R := R) (negPeriod_vadd (N := N) (ι := ι))
  let := NovikovModule.module (R := R) (negPeriod_vadd (N := N) (ι := κ))
  refine Matrix.ext fun j i => ?_
  simp [LinearMap.toMatrix_apply, NovikovModule.basis_repr_apply,
    coordinates_basisCoordinates_basisCoordinates_symm, NovikovModule.coordinates_basis]

end ChangeOfBasis

section CauchyProduct

variable {R V W H ι κ : Type*} [AddCommGroup H]

/-- With the lifts `⟨i, 0⟩`, the Cauchy kernel is the kernel
`TauCeti.NovikovModule.kernelOfMatrix` of the constant matrix with entry `1` at
`((i, j), i, j)` and `0` elsewhere. -/
theorem cauchyKernel_eq_kernelOfMatrix [Semiring R] [DecidableEq ι] [DecidableEq κ]
    (N : H →+ ℝ) :
    cauchyKernel (R := R) (ι := ι) (κ := κ) =
      NovikovModule.kernelOfMatrix (fun _ => (0 : H)) (fun _ => (0 : H)) (fun _ => (0 : H))
        (fun i j k => if k = (i, j) then (1 : NovikovSeries R H N) else 0) := by
  classical
  funext ⟨i, A⟩ ⟨j, A'⟩ ⟨k, C⟩
  rw [cauchyKernel_apply, NovikovModule.kernelOfMatrix_apply]
  by_cases hk : k = (i, j)
  · subst hk
    simp [coeff_one, sub_sub, sub_eq_zero]
  · simp [hk]

/-- **The Cauchy product in basis coordinates** is the Novikov-bilinear product
`TauCeti.NovikovModule.novikovProductOfMatrix` of the constant matrix with entry `1` at
`((i, j), i, j)` and `0` elsewhere, relative to the lifts `⟨i, 0⟩`, `⟨j, 0⟩` and `⟨(i, j), 0⟩`. -/
theorem basisCoordinates_cauchyProduct_eq_novikovProductOfMatrix [CommSemiring R]
    [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] {N : H →+ ℝ} (b : Module.Basis ι R V)
    (c : Module.Basis κ R W) (v : NovikovSeries V H N) (w : NovikovSeries W H N) :
    basisCoordinates (b.tensorProduct c) (cauchyProduct R v w) =
      NovikovModule.novikovProductOfMatrix negPeriod_vadd negPeriod_vadd negPeriod_vadd
        (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun i j k => if k = (i, j) then 1 else 0)
        (basisCoordinates b v) (basisCoordinates c w) := by
  ext p₀
  rw [basisCoordinates_cauchyProduct, NovikovModule.kernelProduct_apply_val,
    NovikovModule.novikovProductOfMatrix_apply_val, cauchyKernel_eq_kernelOfMatrix N]

end CauchyProduct

end NovikovSeries

end TauCeti
