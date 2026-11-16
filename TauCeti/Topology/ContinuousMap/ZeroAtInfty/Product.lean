/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Discrete
public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Products, tensorial maps, and bilinear pairings on `C₀`

For topological spaces `α` and `β`, a scalar function `f ∈ C₀(α, R)` and a vector-valued function
`g ∈ C₀(β, E)` over a seminormed ring `R` with a bounded action on `E` have an elementary tensor
`ZeroAtInftyContinuousMap.prodSMul f g ∈ C₀(α × β, E)`, given by `(x, y) ↦ f x • g y`. Vanishing
at infinity on the product holds without local compactness, since `cocompact (α × β)` is the
coproduct of `cocompact α` and `cocompact β` and both `f` and `g` are bounded. When the action is
norm-multiplicative, `‖prodSMul f g‖ = ‖f‖ * ‖g‖`.

On discrete index types `I` and `J`, currying (`ZeroAtInftyContinuousMap.curryEquiv`) identifies
`C₀(I × J, E)` isometrically with `C₀(I, C₀(J, E))`, the completed tensor product of the model
spaces `C₀(I, R)` and `C₀(J, E)`. This file develops the functorial operations and dual pairings on
such product spaces.

## Main definitions

* `ZeroAtInftyContinuousMap.prodSMul`: elementary tensor `(x, y) ↦ f x • g y` in `C₀(α × β, E)`.
* `ZeroAtInftyContinuousMap.contractSnd`: apply a uniformly bounded linear map `C₀(J, E) →L[S] F`
  in the second variable, producing `C₀(I × J, E) →L[S] C₀(I, F)`.
* `ZeroAtInftyContinuousMap.sndMapCLM`, `ZeroAtInftyContinuousMap.fstMapCLM`, and
  `ZeroAtInftyContinuousMap.prodMapCLM`: apply uniformly bounded operators along the second factor,
  the first factor, or both factors in succession.
* `ZeroAtInftyContinuousMap.prodPairing`: over a nontrivially normed field `K`, combine two
  continuous linear functionals `u ∈ C₀(I, K)*` and `v ∈ C₀(J, K)*` into a functional
  `u ⊗ v ∈ C₀(I × J, K)*`.

## Main results

* `ZeroAtInftyContinuousMap.norm_prodSMul`: `‖prodSMul f g‖ = ‖f‖ * ‖g‖` for norm-multiplicative
  actions.
* `ZeroAtInftyContinuousMap.prodPairing_prodSMul`: `(prodPairing u v) (prodSMul f g) = u f * v g`.
* `ZeroAtInftyContinuousMap.norm_prodPairing`: `‖prodPairing u v‖ = ‖u‖ * ‖v‖`.
* `ZeroAtInftyContinuousMap.prodPairing_comp_congrLeft_prodComm`: symmetry under swapping factors.
* `ZeroAtInftyContinuousMap.prodPairing_comp_prodMapCLM`: naturality with respect to `prodMapCLM`.
* `ZeroAtInftyContinuousMap.prodPairing_comp_congrLeft_prodAssoc`: associativity on triple products.

## References

* P. Schneider, *Nonarchimedean Functional Analysis*, Springer, 2002, §§10, 17.
* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS 12 (1962), 69–85.
-/

public section

open Filter Topology
open scoped ZeroAtInfty

namespace ZeroAtInftyContinuousMap

/-! ### Elementary tensors on product spaces -/

section ProdSMul

variable {α β R E : Type*} [TopologicalSpace α] [TopologicalSpace β]
  [SeminormedRing R] [SeminormedAddCommGroup E] [Module R E] [IsBoundedSMul R E]

private theorem tendsto_cocompact_prodSMul (f : C₀(α, R)) (g : C₀(β, E)) :
    Tendsto (fun p : α × β ↦ f p.1 • g p.2) (cocompact (α × β)) (𝓝 0) := by
  rw [← Filter.coprod_cocompact, Filter.coprod, tendsto_sup]
  refine ⟨?_, ?_⟩
  · refine squeeze_zero_norm
      (fun p ↦ (norm_smul_le (f p.1) (g p.2)).trans
        (mul_le_mul_of_nonneg_left (norm_coe_le_norm g p.2) (norm_nonneg _))) ?_
    simpa using ((zero_at_infty f).norm.comp tendsto_comap).mul_const ‖g‖
  · refine squeeze_zero_norm
      (fun p ↦ (norm_smul_le (f p.1) (g p.2)).trans
        (mul_le_mul_of_nonneg_right (norm_coe_le_norm f p.1) (norm_nonneg _))) ?_
    simpa using ((zero_at_infty g).norm.comp tendsto_comap).const_mul ‖f‖

/-- **Elementary tensor on a product space.** For `f ∈ C₀(α, R)` and `g ∈ C₀(β, E)`, the function
`(x, y) ↦ f x • g y` is continuous and vanishes at infinity on `α × β`. -/
def prodSMul (f : C₀(α, R)) (g : C₀(β, E)) : C₀(α × β, E) where
  toFun p := f p.1 • g p.2
  continuous_toFun := (f.continuous.comp continuous_fst).smul (g.continuous.comp continuous_snd)
  zero_at_infty' := tendsto_cocompact_prodSMul f g

/-- `prodSMul f g` evaluates at `(x, y)` to `f x • g y`. -/
@[simp]
theorem prodSMul_apply (f : C₀(α, R)) (g : C₀(β, E)) (p : α × β) :
    prodSMul f g p = f p.1 • g p.2 := (rfl)

/-- The elementary tensor with zero left factor vanishes. -/
@[simp]
theorem zero_prodSMul (g : C₀(β, E)) : prodSMul (0 : C₀(α, R)) g = 0 := by
  ext; simp

/-- The elementary tensor with zero right factor vanishes. -/
@[simp]
theorem prodSMul_zero (f : C₀(α, R)) : prodSMul f (0 : C₀(β, E)) = 0 := by
  ext; simp

/-- The sup norm of `prodSMul f g` is at most `‖f‖ * ‖g‖`. -/
theorem norm_prodSMul_le (f : C₀(α, R)) (g : C₀(β, E)) :
    ‖prodSMul f g‖ ≤ ‖f‖ * ‖g‖ :=
  (norm_le (by positivity)).2 fun p ↦
    (norm_smul_le (f p.1) (g p.2)).trans
      (mul_le_mul (norm_coe_le_norm f p.1) (norm_coe_le_norm g p.2)
        (norm_nonneg _) (norm_nonneg _))

/-- Elementary tensors distribute over addition in the left factor. -/
theorem add_prodSMul (f₁ f₂ : C₀(α, R)) (g : C₀(β, E)) :
    prodSMul (f₁ + f₂) g = prodSMul f₁ g + prodSMul f₂ g := by
  ext; simp [add_smul]

/-- Elementary tensors distribute over addition in the right factor. -/
theorem prodSMul_add (f : C₀(α, R)) (g₁ g₂ : C₀(β, E)) :
    prodSMul f (g₁ + g₂) = prodSMul f g₁ + prodSMul f g₂ := by
  ext; simp

/-- Elementary tensors commute with compatible scalar multiplication on the right factor. -/
theorem prodSMul_smul {S : Type*} [SMulZeroClass S E] [ContinuousConstSMul S E]
    [SMulCommClass R S E] (s : S) (f : C₀(α, R)) (g : C₀(β, E)) :
    prodSMul f (s • g) = s • prodSMul f g := by
  ext; simp [smul_comm]

/-- Elementary tensors associate with scalar multiplication on the left factor. -/
theorem smul_prodSMul {S : Type*} [SMulZeroClass S R] [ContinuousConstSMul S R]
    [SMulZeroClass S E] [ContinuousConstSMul S E] [IsScalarTower S R E]
    (s : S) (f : C₀(α, R)) (g : C₀(β, E)) :
    prodSMul (s • f) g = s • prodSMul f g := by
  ext; simp [smul_assoc]

/-- Reassociating `(α × β) × γ` to `α × (β × γ)` reassociates iterated elementary tensors. -/
theorem congrLeft_prodAssoc_prodSMul {γ : Type*} [TopologicalSpace γ]
    (f : C₀(α, R)) (g : C₀(β, R)) (h : C₀(γ, E)) :
    congrLeft R E (Homeomorph.prodAssoc α β γ) (prodSMul (prodSMul f g) h) =
      prodSMul f (prodSMul g h) := by
  ext ⟨x, y, z⟩
  simp [Homeomorph.prodAssoc, mul_smul]

end ProdSMul

section ProdSMulExtra

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

/-- When scalar multiplication preserves norms, `‖prodSMul f g‖ = ‖f‖ * ‖g‖`. -/
@[simp]
theorem norm_prodSMul {R E : Type*} [NormedRing R] [NormedAddCommGroup E] [Module R E]
    [NormSMulClass R E] (f : C₀(α, R)) (g : C₀(β, E)) :
    ‖prodSMul f g‖ = ‖f‖ * ‖g‖ := by
  refine le_antisymm (norm_prodSMul_le f g) ?_
  rcases (norm_nonneg g).eq_or_lt with hg | hg
  · simp [← hg]
  · rw [← le_div_iff₀ hg]
    refine (norm_le (by positivity)).2 fun x ↦ ?_
    rw [le_div_iff₀ hg]
    rcases (norm_nonneg (f x)).eq_or_lt with hfx | hfx
    · simp [← hfx]
    · rw [← le_div_iff₀' hfx]
      refine (norm_le (by positivity)).2 fun y ↦ ?_
      rw [le_div_iff₀' hfx, ← norm_smul]
      exact norm_coe_le_norm (prodSMul f g) (x, y)

/-- Over a commutative seminormed ring, swapping the factors of `α × β` swaps the factors of an
elementary tensor. -/
theorem congrLeft_prodComm_prodSMul {R : Type*} [SeminormedCommRing R]
    (f : C₀(α, R)) (g : C₀(β, R)) :
    congrLeft R R (Homeomorph.prodComm α β) (prodSMul f g) = prodSMul g f := by
  ext ⟨y, x⟩
  simp [mul_comm]

end ProdSMulExtra

/-! ### Tensorial operators on discrete product spaces -/

section Discrete

variable {I I' J J' L S R E F G : Type*}
  [TopologicalSpace I] [DiscreteTopology I]
  [TopologicalSpace I'] [DiscreteTopology I']
  [TopologicalSpace J] [DiscreteTopology J]
  [TopologicalSpace J'] [DiscreteTopology J']
  [TopologicalSpace L] [DiscreteTopology L]

/-- On discrete index types, the elementary tensor of two coordinate vectors is a coordinate
vector. -/
@[simp]
theorem prodSMul_single [SeminormedRing R] [SeminormedAddCommGroup E]
    [Module R E] [IsBoundedSMul R E] [DecidableEq I] [DecidableEq J]
    (i : I) (r : R) (j : J) (e : E) :
    prodSMul (single i r) (single j e) = single (i, j) (r • e) := by
  ext ⟨i', j'⟩
  by_cases hi : i' = i <;> by_cases hj : j' = j <;> simp [hi, hj]

section Semiring

variable [Semiring S]
  [SeminormedAddCommGroup E] [Module S E] [ContinuousConstSMul S E]
  [SeminormedAddCommGroup F] [Module S F] [ContinuousConstSMul S F]
  [SeminormedAddCommGroup G] [Module S G] [ContinuousConstSMul S G]

/-- Currying an elementary tensor gives the scalar multiples of the right factor by the entries of
the left factor. -/
@[simp]
theorem curryEquiv_prodSMul_apply [SeminormedRing R] [Module R E]
    [IsBoundedSMul R E] (f : C₀(I, R)) (g : C₀(J, E)) (i : I) :
    curryEquiv S E (prodSMul f g) i = f i • g := by
  ext j
  simp

variable (I) in
/-- **Contraction in the second variable.** A continuous linear map `v : C₀(J, E) →L[S] F` with a
uniform bound `‖v g‖ ≤ C * ‖g‖` acts on each row `j ↦ f (i, j)` of `f ∈ C₀(I × J, E)`, giving a
continuous linear map `C₀(I × J, E) →L[S] C₀(I, F)`. -/
noncomputable def contractSnd (v : C₀(J, E) →L[S] F) (hv : ∃ C, ∀ g, ‖v g‖ ≤ C * ‖g‖) :
    C₀(I × J, E) →L[S] C₀(I, F) :=
  compLeft (α := I) v hv ∘L
    (curryEquiv (I := I) (J := J) S E).toLinearIsometry.toContinuousLinearMap

/-- `contractSnd I v hv f` evaluates at `i` by applying `v` to the `i`-th row of `f`. -/
@[simp]
theorem contractSnd_apply (v : C₀(J, E) →L[S] F) (hv : ∃ C, ∀ g, ‖v g‖ ≤ C * ‖g‖)
    (f : C₀(I × J, E)) (i : I) :
    contractSnd I v hv f i = v (curryEquiv S E f i) := by
  simp [contractSnd]

/-- A uniform bound for `v` is also a uniform bound for `contractSnd I v`. -/
theorem norm_contractSnd_apply_le (v : C₀(J, E) →L[S] F) {C : ℝ}
    (hC : ∀ g, ‖v g‖ ≤ C * ‖g‖) (f : C₀(I × J, E)) :
    ‖contractSnd I v ⟨C, hC⟩ f‖ ≤ C * ‖f‖ := by
  rw [contractSnd, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry]
  exact (norm_compLeft_apply_le v hC (curryEquiv S E f)).trans
    (by rw [LinearIsometryEquiv.norm_map])

variable (I) in
/-- **Operator action on the second factor.** A uniformly bounded operator
`v : C₀(J, E) →L[S] C₀(J', F)` induces `C₀(I × J, E) →L[S] C₀(I × J', F)` row by row. -/
noncomputable def sndMapCLM (v : C₀(J, E) →L[S] C₀(J', F)) (hv : ∃ C, ∀ g, ‖v g‖ ≤ C * ‖g‖) :
    C₀(I × J, E) →L[S] C₀(I × J', F) :=
  (curryEquiv (I := I) (J := J') S F).symm.toLinearIsometry.toContinuousLinearMap ∘L
    contractSnd I v hv

/-- `sndMapCLM I v hv f` applies `v` to the `i`-th row of `f`. -/
@[simp]
theorem sndMapCLM_apply (v : C₀(J, E) →L[S] C₀(J', F)) (hv : ∃ C, ∀ g, ‖v g‖ ≤ C * ‖g‖)
    (f : C₀(I × J, E)) (i : I) (j' : J') :
    sndMapCLM I v hv f (i, j') = v (curryEquiv S E f i) j' := by
  simp [sndMapCLM]

/-- Currying `sndMapCLM I v hv f` gives `v` applied to each row of `f`. -/
@[simp]
theorem curryEquiv_sndMapCLM_apply (v : C₀(J, E) →L[S] C₀(J', F))
    (hv : ∃ C, ∀ g, ‖v g‖ ≤ C * ‖g‖) (f : C₀(I × J, E)) (i : I) :
    curryEquiv S F (sndMapCLM I v hv f) i = v (curryEquiv S E f i) := by
  ext j'
  simp

/-- A uniform bound for `v` is also a uniform bound for `sndMapCLM I v`. -/
theorem norm_sndMapCLM_apply_le (v : C₀(J, E) →L[S] C₀(J', F)) {C : ℝ}
    (hC : ∀ g, ‖v g‖ ≤ C * ‖g‖) (f : C₀(I × J, E)) :
    ‖sndMapCLM I v ⟨C, hC⟩ f‖ ≤ C * ‖f‖ := by
  rw [sndMapCLM, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.norm_map]
  exact norm_contractSnd_apply_le v hC f

/-- `sndMapCLM` is itself uniformly bounded. -/
theorem exists_norm_sndMapCLM_apply_le (v : C₀(J, E) →L[S] C₀(J', F))
    (hv : ∃ C, ∀ g, ‖v g‖ ≤ C * ‖g‖) :
    ∃ C, ∀ f : C₀(I × J, E), ‖sndMapCLM I v hv f‖ ≤ C * ‖f‖ := by
  obtain ⟨C, hC⟩ := hv
  refine ⟨max C 0, fun f ↦ ?_⟩
  have hC' : ∀ g, ‖v g‖ ≤ max C 0 * ‖g‖ := fun g ↦
    (hC g).trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (norm_nonneg g))
  exact norm_sndMapCLM_apply_le (I := I) v hC' f

/-- The identity operator induces the identity on the second factor. -/
@[simp]
theorem sndMapCLM_id (h : ∃ C, ∀ g : C₀(J, E), ‖ContinuousLinearMap.id S _ g‖ ≤ C * ‖g‖) :
    sndMapCLM I (ContinuousLinearMap.id S C₀(J, E)) h = ContinuousLinearMap.id S _ := by
  ext f ⟨i, j⟩
  simp

/-- `sndMapCLM` respects operator composition. -/
theorem sndMapCLM_comp (w : C₀(J', F) →L[S] C₀(L, G)) (v : C₀(J, E) →L[S] C₀(J', F))
    (hw : ∃ C, ∀ g, ‖w g‖ ≤ C * ‖g‖) (hv : ∃ C, ∀ g, ‖v g‖ ≤ C * ‖g‖)
    (hwv : ∃ C, ∀ g, ‖w.comp v g‖ ≤ C * ‖g‖) :
    sndMapCLM I (w.comp v) hwv = (sndMapCLM I w hw).comp (sndMapCLM I v hv) := by
  ext f ⟨i, l⟩
  simp

/-- On a coordinate vector `single (i, j) e`, `sndMapCLM` acts on `single j e` in the `i`-th row
and vanishes on all other rows. -/
theorem sndMapCLM_single [DecidableEq I] [DecidableEq J]
    (v : C₀(J, E) →L[S] C₀(J', F)) (hv : ∃ C, ∀ g, ‖v g‖ ≤ C * ‖g‖)
    (i : I) (j : J) (e : E) :
    sndMapCLM I v hv (single (i, j) e) =
      (curryEquiv S F).symm (single i (v (single j e))) := by
  ext ⟨i', j'⟩
  by_cases hi : i' = i <;> simp [hi]

variable (J) in
/-- **Operator action on the first factor.** A uniformly bounded operator
`u : C₀(I, E) →L[S] C₀(I', F)` induces `C₀(I × J, E) →L[S] C₀(I' × J, F)` column by column,
obtained from `sndMapCLM` by swapping the product factors. -/
noncomputable def fstMapCLM (u : C₀(I, E) →L[S] C₀(I', F)) (hu : ∃ C, ∀ f, ‖u f‖ ≤ C * ‖f‖) :
    C₀(I × J, E) →L[S] C₀(I' × J, F) :=
  (congrLeft S F (Homeomorph.prodComm J I')).toLinearIsometry.toContinuousLinearMap ∘L
    sndMapCLM J u hu ∘L
      (congrLeft S E (Homeomorph.prodComm I J)).toLinearIsometry.toContinuousLinearMap

/-- `fstMapCLM J u hu f` applies `u` to the `j`-th column of `f`. -/
@[simp]
theorem fstMapCLM_apply (u : C₀(I, E) →L[S] C₀(I', F)) (hu : ∃ C, ∀ f, ‖u f‖ ≤ C * ‖f‖)
    (f : C₀(I × J, E)) (i' : I') (j : J) :
    fstMapCLM J u hu f (i', j) =
      u (curryEquiv S E (congrLeft S E (Homeomorph.prodComm I J) f) j) i' := by
  simp [fstMapCLM]

/-- A uniform bound for `u` is also a uniform bound for `fstMapCLM J u`. -/
theorem norm_fstMapCLM_apply_le (u : C₀(I, E) →L[S] C₀(I', F)) {C : ℝ}
    (hC : ∀ f, ‖u f‖ ≤ C * ‖f‖) (f : C₀(I × J, E)) :
    ‖fstMapCLM J u ⟨C, hC⟩ f‖ ≤ C * ‖f‖ := by
  simp only [fstMapCLM, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.norm_map]
  exact (norm_sndMapCLM_apply_le u hC _).trans (by rw [LinearIsometryEquiv.norm_map])

/-- `fstMapCLM` is itself uniformly bounded. -/
theorem exists_norm_fstMapCLM_apply_le (u : C₀(I, E) →L[S] C₀(I', F))
    (hu : ∃ C, ∀ f, ‖u f‖ ≤ C * ‖f‖) :
    ∃ C, ∀ f : C₀(I × J, E), ‖fstMapCLM J u hu f‖ ≤ C * ‖f‖ := by
  obtain ⟨C, hC⟩ := hu
  refine ⟨max C 0, fun f ↦ ?_⟩
  have hC' : ∀ g, ‖u g‖ ≤ max C 0 * ‖g‖ := fun g ↦
    (hC g).trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (norm_nonneg g))
  exact norm_fstMapCLM_apply_le (J := J) u hC' f

/-- The identity operator induces the identity on the first factor. -/
@[simp]
theorem fstMapCLM_id (h : ∃ C, ∀ f : C₀(I, E), ‖ContinuousLinearMap.id S _ f‖ ≤ C * ‖f‖) :
    fstMapCLM J (ContinuousLinearMap.id S C₀(I, E)) h = ContinuousLinearMap.id S _ := by
  ext f ⟨i, j⟩
  simp

/-- `fstMapCLM` respects operator composition. -/
theorem fstMapCLM_comp (w : C₀(I', F) →L[S] C₀(L, G)) (u : C₀(I, E) →L[S] C₀(I', F))
    (hw : ∃ C, ∀ f, ‖w f‖ ≤ C * ‖f‖) (hu : ∃ C, ∀ f, ‖u f‖ ≤ C * ‖f‖)
    (hwu : ∃ C, ∀ f, ‖w.comp u f‖ ≤ C * ‖f‖) :
    fstMapCLM J (w.comp u) hwu = (fstMapCLM J w hw).comp (fstMapCLM J u hu) := by
  ext f ⟨l, j⟩
  have hswap : congrLeft S F (Homeomorph.prodComm I' J)
      (congrLeft S F (Homeomorph.prodComm J I')
        (sndMapCLM J u hu (congrLeft S E (Homeomorph.prodComm I J) f))) =
      sndMapCLM J u hu (congrLeft S E (Homeomorph.prodComm I J) f) := by
    ext ⟨j', i'⟩; simp
  simp [fstMapCLM, hswap]

/-- **Product of two operators.** Uniformly bounded operators `u : C₀(I, E) →L[S] C₀(I', F)` and
`v : C₀(J, F) →L[S] C₀(J', G)` combine into `C₀(I × J, E) →L[S] C₀(I' × J', G)`. -/
noncomputable def prodMapCLM (u : C₀(I, E) →L[S] C₀(I', F)) (hu : ∃ C, ∀ f, ‖u f‖ ≤ C * ‖f‖)
    (v : C₀(J, F) →L[S] C₀(J', G)) (hv : ∃ C, ∀ g, ‖v g‖ ≤ C * ‖g‖) :
    C₀(I × J, E) →L[S] C₀(I' × J', G) :=
  sndMapCLM I' v hv ∘L fstMapCLM J u hu

/-- `prodMapCLM` factors as `sndMapCLM` after `fstMapCLM`. -/
theorem prodMapCLM_def (u : C₀(I, E) →L[S] C₀(I', F)) (hu : ∃ C, ∀ f, ‖u f‖ ≤ C * ‖f‖)
    (v : C₀(J, F) →L[S] C₀(J', G)) (hv : ∃ C, ∀ g, ‖v g‖ ≤ C * ‖g‖) :
    prodMapCLM u hu v hv = sndMapCLM I' v hv ∘L fstMapCLM J u hu := (rfl)

/-- A product of nonnegative bounds for `u` and `v` bounds `prodMapCLM u _ v _`. -/
theorem norm_prodMapCLM_apply_le (u : C₀(I, E) →L[S] C₀(I', F))
    (v : C₀(J, F) →L[S] C₀(J', G)) {C₁ C₂ : ℝ} (hC₂ : 0 ≤ C₂)
    (hu : ∀ f, ‖u f‖ ≤ C₁ * ‖f‖) (hv : ∀ g, ‖v g‖ ≤ C₂ * ‖g‖) (f : C₀(I × J, E)) :
    ‖prodMapCLM u ⟨C₁, hu⟩ v ⟨C₂, hv⟩ f‖ ≤ C₂ * C₁ * ‖f‖ := by
  rw [prodMapCLM, ContinuousLinearMap.comp_apply, mul_assoc]
  exact (norm_sndMapCLM_apply_le v hv _).trans
    (mul_le_mul_of_nonneg_left (norm_fstMapCLM_apply_le u hu f) hC₂)

/-- If `v` and `v'` intertwine bounded coefficient maps `w₁` and `w₂`, so do `sndMapCLM I v` and
`sndMapCLM I v'`. -/
theorem compLeft_sndMapCLM {E' F' : Type*}
    [SeminormedAddCommGroup E'] [Module S E'] [ContinuousConstSMul S E']
    [SeminormedAddCommGroup F'] [Module S F'] [ContinuousConstSMul S F']
    (w₁ : E →L[S] E') (hw₁ : ∃ C, ∀ e, ‖w₁ e‖ ≤ C * ‖e‖)
    (w₂ : F →L[S] F') (hw₂ : ∃ C, ∀ f, ‖w₂ f‖ ≤ C * ‖f‖)
    (v : C₀(J, E) →L[S] C₀(J', F)) (hv : ∃ C, ∀ g, ‖v g‖ ≤ C * ‖g‖)
    (v' : C₀(J, E') →L[S] C₀(J', F')) (hv' : ∃ C, ∀ g, ‖v' g‖ ≤ C * ‖g‖)
    (hinter : compLeft (α := J') w₂ hw₂ ∘L v = v' ∘L compLeft (α := J) w₁ hw₁)
    (f : C₀(I × J, E)) :
    compLeft w₂ hw₂ (sndMapCLM I v hv f) = sndMapCLM I v' hv' (compLeft w₁ hw₁ f) := by
  ext ⟨i, j'⟩
  have hi := congr($(hinter) (curryEquiv S E f i) j')
  simpa [curryEquiv_compLeft] using hi

/-- If `u` and `u'` intertwine bounded coefficient maps `w₁` and `w₂`, so do `fstMapCLM J u` and
`fstMapCLM J u'`. -/
theorem compLeft_fstMapCLM {E' F' : Type*}
    [SeminormedAddCommGroup E'] [Module S E'] [ContinuousConstSMul S E']
    [SeminormedAddCommGroup F'] [Module S F'] [ContinuousConstSMul S F']
    (w₁ : E →L[S] E') (hw₁ : ∃ C, ∀ e, ‖w₁ e‖ ≤ C * ‖e‖)
    (w₂ : F →L[S] F') (hw₂ : ∃ C, ∀ f, ‖w₂ f‖ ≤ C * ‖f‖)
    (u : C₀(I, E) →L[S] C₀(I', F)) (hu : ∃ C, ∀ g, ‖u g‖ ≤ C * ‖g‖)
    (u' : C₀(I, E') →L[S] C₀(I', F')) (hu' : ∃ C, ∀ g, ‖u' g‖ ≤ C * ‖g‖)
    (hinter : compLeft (α := I') w₂ hw₂ ∘L u = u' ∘L compLeft (α := I) w₁ hw₁)
    (f : C₀(I × J, E)) :
    compLeft w₂ hw₂ (fstMapCLM J u hu f) = fstMapCLM J u' hu' (compLeft w₁ hw₁ f) := by
  simp only [fstMapCLM, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, ← congrLeft_compLeft]
  rw [compLeft_sndMapCLM w₁ hw₁ w₂ hw₂ u hu u' hu' hinter, congrLeft_compLeft]

end Semiring

section CommRing

variable {R : Type*} [SeminormedCommRing R]

/-- Over a commutative seminormed ring, `sndMapCLM` acts on the second factor of an elementary
tensor. -/
@[simp]
theorem sndMapCLM_prodSMul (v : C₀(J, R) →L[R] C₀(J', R)) (hv : ∃ C, ∀ g, ‖v g‖ ≤ C * ‖g‖)
    (f : C₀(I, R)) (g : C₀(J, R)) :
    sndMapCLM I v hv (prodSMul f g) = prodSMul f (v g) := by
  ext ⟨i, j'⟩
  simp [curryEquiv_prodSMul_apply (S := R)]

/-- Over a commutative seminormed ring, `fstMapCLM` acts on the first factor of an elementary
tensor. -/
@[simp]
theorem fstMapCLM_prodSMul (u : C₀(I, R) →L[R] C₀(I', R)) (hu : ∃ C, ∀ f, ‖u f‖ ≤ C * ‖f‖)
    (f : C₀(I, R)) (g : C₀(J, R)) :
    fstMapCLM J u hu (prodSMul f g) = prodSMul (u f) g := by
  ext ⟨i', j⟩
  simp [congrLeft_prodComm_prodSMul, curryEquiv_prodSMul_apply (S := R), mul_comm]

/-- Over a commutative seminormed ring, `prodMapCLM` acts factorwise on elementary tensors. -/
@[simp]
theorem prodMapCLM_prodSMul (u : C₀(I, R) →L[R] C₀(I', R)) (hu : ∃ C, ∀ f, ‖u f‖ ≤ C * ‖f‖)
    (v : C₀(J, R) →L[R] C₀(J', R)) (hv : ∃ C, ∀ g, ‖v g‖ ≤ C * ‖g‖)
    (f : C₀(I, R)) (g : C₀(J, R)) :
    prodMapCLM u hu v hv (prodSMul f g) = prodSMul (u f) (v g) := by
  simp [prodMapCLM]

end CommRing

/-! ### Bilinear pairing of continuous linear functionals -/

section ProdPairing

variable {K : Type*} [NontriviallyNormedField K]

/-- **Product of two continuous linear functionals.** Over a nontrivially normed field `K`, two
continuous linear functionals `u ∈ C₀(I, K)*` and `v ∈ C₀(J, K)*` combine into a continuous linear
functional `prodPairing u v ∈ C₀(I × J, K)*` by applying `v` to each row and then `u` across the
rows. No completeness or ultrametric hypothesis on `K` is needed. -/
noncomputable def prodPairing (u : C₀(I, K) →L[K] K) (v : C₀(J, K) →L[K] K) :
    C₀(I × J, K) →L[K] K :=
  u ∘L contractSnd I v ⟨‖v‖, v.le_opNorm⟩

/-- `prodPairing u v` applies `v` along each row and then `u` to the resulting family. -/
theorem prodPairing_apply (u : C₀(I, K) →L[K] K) (v : C₀(J, K) →L[K] K) (f : C₀(I × J, K)) :
    prodPairing u v f = u (contractSnd I v ⟨‖v‖, v.le_opNorm⟩ f) := (rfl)

/-- Pairing with the zero functional on the left gives zero. -/
@[simp]
theorem prodPairing_zero_left (v : C₀(J, K) →L[K] K) :
    prodPairing (0 : C₀(I, K) →L[K] K) v = 0 := by
  ext f; simp [prodPairing_apply]

/-- Pairing with the zero functional on the right gives zero. -/
@[simp]
theorem prodPairing_zero_right (u : C₀(I, K) →L[K] K) :
    prodPairing u (0 : C₀(J, K) →L[K] K) = 0 := by
  ext f
  have hrow : contractSnd I (0 : C₀(J, K) →L[K] K) ⟨‖(0 : C₀(J, K) →L[K] K)‖,
      ContinuousLinearMap.le_opNorm 0⟩ f = 0 := by
    ext i; simp
  rw [prodPairing_apply, hrow, map_zero, zero_apply]

/-- `prodPairing` is additive in the left functional. -/
theorem prodPairing_add_left (u₁ u₂ : C₀(I, K) →L[K] K) (v : C₀(J, K) →L[K] K) :
    prodPairing (u₁ + u₂) v = prodPairing u₁ v + prodPairing u₂ v := by
  ext f; rfl

/-- `prodPairing` is additive in the right functional. -/
theorem prodPairing_add_right (u : C₀(I, K) →L[K] K) (v₁ v₂ : C₀(J, K) →L[K] K) :
    prodPairing u (v₁ + v₂) = prodPairing u v₁ + prodPairing u v₂ := by
  ext f
  have hrow : contractSnd I (v₁ + v₂) ⟨‖v₁ + v₂‖, (v₁ + v₂).le_opNorm⟩ f =
      contractSnd I v₁ ⟨‖v₁‖, v₁.le_opNorm⟩ f +
        contractSnd I v₂ ⟨‖v₂‖, v₂.le_opNorm⟩ f := by
    ext i; simp
  rw [prodPairing_apply, hrow, map_add, _root_.add_apply, prodPairing_apply, prodPairing_apply]

/-- `prodPairing` is `K`-linear in the left functional. -/
theorem prodPairing_smul_left (c : K) (u : C₀(I, K) →L[K] K) (v : C₀(J, K) →L[K] K) :
    prodPairing (c • u) v = c • prodPairing u v := by
  ext f; rfl

/-- `prodPairing` is `K`-linear in the right functional. -/
theorem prodPairing_smul_right (c : K) (u : C₀(I, K) →L[K] K) (v : C₀(J, K) →L[K] K) :
    prodPairing u (c • v) = c • prodPairing u v := by
  ext f
  have hrow : contractSnd I (c • v) ⟨‖c • v‖, (c • v).le_opNorm⟩ f =
      c • contractSnd I v ⟨‖v‖, v.le_opNorm⟩ f := by
    ext i; simp
  rw [prodPairing_apply, hrow, map_smul, _root_.smul_apply, prodPairing_apply]

/-- `prodPairing` commutes with negation in the left functional. -/
@[simp]
theorem prodPairing_neg_left (u : C₀(I, K) →L[K] K) (v : C₀(J, K) →L[K] K) :
    prodPairing (-u) v = -prodPairing u v := by
  ext f; rfl

/-- `prodPairing` commutes with negation in the right functional. -/
@[simp]
theorem prodPairing_neg_right (u : C₀(I, K) →L[K] K) (v : C₀(J, K) →L[K] K) :
    prodPairing u (-v) = -prodPairing u v := by
  ext f
  have hrow : contractSnd I (-v) ⟨‖-v‖, (-v).le_opNorm⟩ f =
      -contractSnd I v ⟨‖v‖, v.le_opNorm⟩ f := by
    ext i; simp
  rw [prodPairing_apply, hrow, map_neg, _root_.neg_apply, prodPairing_apply]

/-- On an elementary tensor `prodSMul f g`, the product functional evaluates to `u f * v g`. -/
@[simp]
theorem prodPairing_prodSMul (u : C₀(I, K) →L[K] K) (v : C₀(J, K) →L[K] K)
    (f : C₀(I, K)) (g : C₀(J, K)) :
    prodPairing u v (prodSMul f g) = u f * v g := by
  have hrow : contractSnd I v ⟨‖v‖, v.le_opNorm⟩ (prodSMul f g) = v g • f := by
    ext i
    simp [mul_comm]
  rw [prodPairing_apply, hrow, map_smul, smul_eq_mul, mul_comm]

/-- On a coordinate vector `single (i, j) a`, the product functional evaluates to
`a * (u (single i 1) * v (single j 1))`. -/
theorem prodPairing_single [DecidableEq I] [DecidableEq J]
    (u : C₀(I, K) →L[K] K) (v : C₀(J, K) →L[K] K) (i : I) (j : J) (a : K) :
    prodPairing u v (single (i, j) a) = a * (u (single i 1) * v (single j 1)) := by
  have h : single (i, j) a = a • prodSMul (single i (1 : K)) (single j (1 : K)) := by
    rw [prodSMul_single, smul_eq_mul, mul_one, ← single_smul, smul_eq_mul, mul_one]
  rw [h, map_smul, prodPairing_prodSMul, smul_eq_mul]

/-- **Exact norm of the product functional**: `‖prodPairing u v‖ = ‖u‖ * ‖v‖`. -/
@[simp]
theorem norm_prodPairing (u : C₀(I, K) →L[K] K) (v : C₀(J, K) →L[K] K) :
    ‖prodPairing u v‖ = ‖u‖ * ‖v‖ := by
  have hp : 0 ≤ ‖prodPairing u v‖ := ContinuousLinearMap.opNorm_nonneg (prodPairing u v)
  have hu0 : 0 ≤ ‖u‖ := ContinuousLinearMap.opNorm_nonneg u
  have hv0 : 0 ≤ ‖v‖ := ContinuousLinearMap.opNorm_nonneg v
  refine le_antisymm ?_ ?_
  · refine (prodPairing u v).opNorm_le_bound (mul_nonneg hu0 hv0) fun f ↦ ?_
    rw [prodPairing_apply, mul_assoc]
    exact (u.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (norm_contractSnd_apply_le v v.le_opNorm f) hu0)
  · rcases hu0.eq_or_lt with hu | hu
    · rw [← hu, zero_mul]
      exact hp
    · rw [← le_div_iff₀' hu]
      refine v.opNorm_le_bound (div_nonneg hp hu.le) fun g ↦ ?_
      rw [div_mul_eq_mul_div, le_div_iff₀ hu, mul_comm ‖v g‖ ‖u‖]
      rcases (norm_nonneg (v g)).eq_or_lt with hvg | hvg
      · rw [← hvg, mul_zero]
        exact mul_nonneg hp (norm_nonneg g)
      · rw [← le_div_iff₀ hvg]
        refine u.opNorm_le_bound (div_nonneg (mul_nonneg hp (norm_nonneg g)) hvg.le) fun f ↦ ?_
        rw [div_mul_eq_mul_div, le_div_iff₀ hvg]
        calc ‖u f‖ * ‖v g‖
          _ = ‖prodPairing u v (prodSMul f g)‖ := by rw [← norm_mul, prodPairing_prodSMul]
          _ ≤ ‖prodPairing u v‖ * ‖prodSMul f g‖ := (prodPairing u v).le_opNorm _
          _ = ‖prodPairing u v‖ * ‖g‖ * ‖f‖ := by rw [norm_prodSMul]; ring

/-- **Fubini symmetry for `prodPairing`.** Swapping the factors of `I × J` swaps the order in which
two continuous linear functionals are applied, over any nontrivially normed field `K`. -/
theorem prodPairing_comp_congrLeft_prodComm (u : C₀(I, K) →L[K] K) (v : C₀(J, K) →L[K] K) :
    prodPairing v u ∘L
        (congrLeft K K (Homeomorph.prodComm I J)).toLinearIsometry.toContinuousLinearMap =
      prodPairing u v := by
  classical
  refine continuousLinearMap_ext_single_one fun p ↦ ?_
  rcases p with ⟨i, j⟩
  have h1 : single (i, j) (1 : K) = prodSMul (single i (1 : K)) (single j (1 : K)) := by simp
  rw [h1, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, congrLeft_prodComm_prodSMul, prodPairing_prodSMul,
    prodPairing_prodSMul, mul_comm]

/-- Pointwise form of Fubini symmetry for `prodPairing`. -/
theorem prodPairing_congrLeft_prodComm (u : C₀(I, K) →L[K] K) (v : C₀(J, K) →L[K] K)
    (f : C₀(I × J, K)) :
    prodPairing v u (congrLeft K K (Homeomorph.prodComm I J) f) = prodPairing u v f :=
  congr($(prodPairing_comp_congrLeft_prodComm u v) f)

/-- **Naturality of `prodPairing`** with respect to `prodMapCLM`. -/
theorem prodPairing_comp_prodMapCLM
    (u : C₀(I', K) →L[K] K) (v : C₀(J', K) →L[K] K)
    (T₁ : C₀(I, K) →L[K] C₀(I', K)) (hT₁ : ∃ C, ∀ f, ‖T₁ f‖ ≤ C * ‖f‖)
    (T₂ : C₀(J, K) →L[K] C₀(J', K)) (hT₂ : ∃ C, ∀ g, ‖T₂ g‖ ≤ C * ‖g‖) :
    prodPairing u v ∘L prodMapCLM T₁ hT₁ T₂ hT₂ =
      prodPairing (u ∘L T₁) (v ∘L T₂) := by
  classical
  refine continuousLinearMap_ext_single_one fun p ↦ ?_
  rcases p with ⟨i, j⟩
  have h1 : single (i, j) (1 : K) = prodSMul (single i (1 : K)) (single j (1 : K)) := by simp
  rw [h1, ContinuousLinearMap.comp_apply, prodMapCLM_prodSMul, prodPairing_prodSMul,
    prodPairing_prodSMul, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]

/-- Naturality of `prodPairing` in the first factor. -/
theorem prodPairing_comp_fstMapCLM
    (u : C₀(I', K) →L[K] K) (v : C₀(J, K) →L[K] K)
    (T₁ : C₀(I, K) →L[K] C₀(I', K)) (hT₁ : ∃ C, ∀ f, ‖T₁ f‖ ≤ C * ‖f‖) :
    prodPairing u v ∘L fstMapCLM J T₁ hT₁ = prodPairing (u ∘L T₁) v := by
  have hid : ∃ C, ∀ g : C₀(J, K), ‖ContinuousLinearMap.id K _ g‖ ≤ C * ‖g‖ :=
    ⟨1, fun g ↦ by simp⟩
  simpa [prodMapCLM, sndMapCLM_id] using
    prodPairing_comp_prodMapCLM u v T₁ hT₁ (ContinuousLinearMap.id K C₀(J, K)) hid

/-- Naturality of `prodPairing` in the second factor. -/
theorem prodPairing_comp_sndMapCLM
    (u : C₀(I, K) →L[K] K) (v : C₀(J', K) →L[K] K)
    (T₂ : C₀(J, K) →L[K] C₀(J', K)) (hT₂ : ∃ C, ∀ g, ‖T₂ g‖ ≤ C * ‖g‖) :
    prodPairing u v ∘L sndMapCLM I T₂ hT₂ = prodPairing u (v ∘L T₂) := by
  have hid : ∃ C, ∀ f : C₀(I, K), ‖ContinuousLinearMap.id K _ f‖ ≤ C * ‖f‖ :=
    ⟨1, fun f ↦ by simp⟩
  simpa [prodMapCLM, fstMapCLM_id] using
    prodPairing_comp_prodMapCLM u v (ContinuousLinearMap.id K C₀(I, K)) hid T₂ hT₂

/-- **Associativity of `prodPairing`** along `Homeomorph.prodAssoc`. -/
theorem prodPairing_comp_congrLeft_prodAssoc
    (u : C₀(I, K) →L[K] K) (v : C₀(J, K) →L[K] K) (w : C₀(L, K) →L[K] K) :
    prodPairing u (prodPairing v w) ∘L
        (congrLeft K K (Homeomorph.prodAssoc I J L)).toLinearIsometry.toContinuousLinearMap =
      prodPairing (prodPairing u v) w := by
  classical
  refine continuousLinearMap_ext_single_one fun p ↦ ?_
  rcases p with ⟨⟨i, j⟩, l⟩
  have h1 : single ((i, j), l) (1 : K) =
      prodSMul (prodSMul (single i (1 : K)) (single j (1 : K))) (single l (1 : K)) := by
    simp
  rw [h1, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, congrLeft_prodAssoc_prodSMul, prodPairing_prodSMul,
    prodPairing_prodSMul, prodPairing_prodSMul, prodPairing_prodSMul, mul_assoc]

end ProdPairing

end Discrete

end ZeroAtInftyContinuousMap
