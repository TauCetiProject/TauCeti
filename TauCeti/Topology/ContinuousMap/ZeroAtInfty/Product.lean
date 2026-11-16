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

For topological spaces `α` and `β`, `f ∈ C₀(α, R)` and `g ∈ C₀(β, E)` form the elementary tensor
`ZeroAtInftyContinuousMap.prodSMul f g ∈ C₀(α × β, E)` (`(x, y) ↦ f x • g y`), with
`‖prodSMul f g‖ = ‖f‖ * ‖g‖` for norm-multiplicative actions. On discrete index types `I` and `J`,
currying (`curryEquiv`) identifies `C₀(I × J, E)` isometrically with `C₀(I, C₀(J, E))`, yielding
the functorial operators `contractSnd`, `sndMapCLM`, `fstMapCLM`, `prodMapCLM` and the product
functional `prodPairing : C₀(I, K)* → C₀(J, K)* → C₀(I × J, K)*` with
`‖prodPairing u v‖ = ‖u‖ * ‖v‖` and Fubini symmetry, naturality, and associativity laws.

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

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

section BoundedSMul

variable {R E : Type*} [SeminormedRing R] [SeminormedAddCommGroup E] [Module R E]
  [IsBoundedSMul R E]

private theorem tendsto_cocompact_prodSMul (f : C₀(α, R)) (g : C₀(β, E)) :
    Tendsto (fun p : α × β ↦ f p.1 • g p.2) (cocompact (α × β)) (𝓝 0) := by
  rw [← Filter.coprod_cocompact, Filter.coprod, tendsto_sup]
  exact ⟨squeeze_zero_norm (fun p ↦ (norm_smul_le _ _).trans
      (mul_le_mul_of_nonneg_left (norm_coe_le_norm g p.2) (norm_nonneg _)))
      (by simpa using ((zero_at_infty f).norm.comp tendsto_comap).mul_const ‖g‖),
    squeeze_zero_norm (fun p ↦ (norm_smul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_coe_le_norm f p.1) (norm_nonneg _)))
      (by simpa using ((zero_at_infty g).norm.comp tendsto_comap).const_mul ‖f‖)⟩

/-- **Elementary tensor on a product space**: `(x, y) ↦ f x • g y` in `C₀(α × β, E)`. -/
def prodSMul (f : C₀(α, R)) (g : C₀(β, E)) : C₀(α × β, E) where
  toFun p := f p.1 • g p.2
  continuous_toFun := (f.continuous.comp continuous_fst).smul (g.continuous.comp continuous_snd)
  zero_at_infty' := tendsto_cocompact_prodSMul f g

/-- `prodSMul f g` evaluates at `(x, y)` to `f x • g y`. -/
@[simp] theorem prodSMul_apply (f : C₀(α, R)) (g : C₀(β, E)) (p : α × β) :
    prodSMul f g p = f p.1 • g p.2 := (rfl)

/-- The elementary tensor with zero left factor vanishes. -/
@[simp] theorem zero_prodSMul (g : C₀(β, E)) : prodSMul (0 : C₀(α, R)) g = 0 := by ext; simp

/-- The elementary tensor with zero right factor vanishes. -/
@[simp] theorem prodSMul_zero (f : C₀(α, R)) : prodSMul f (0 : C₀(β, E)) = 0 := by ext; simp

/-- The sup norm of `prodSMul f g` is at most `‖f‖ * ‖g‖`. -/
theorem norm_prodSMul_le (f : C₀(α, R)) (g : C₀(β, E)) : ‖prodSMul f g‖ ≤ ‖f‖ * ‖g‖ :=
  (norm_le (by positivity)).2 fun p ↦ (norm_smul_le (f p.1) (g p.2)).trans
    (mul_le_mul (norm_coe_le_norm f p.1) (norm_coe_le_norm g p.2) (norm_nonneg _) (norm_nonneg _))

/-- Elementary tensors distribute over addition in the left factor. -/
theorem add_prodSMul (f₁ f₂ : C₀(α, R)) (g : C₀(β, E)) :
    prodSMul (f₁ + f₂) g = prodSMul f₁ g + prodSMul f₂ g := by ext; simp [add_smul]

/-- Elementary tensors distribute over addition in the right factor. -/
theorem prodSMul_add (f : C₀(α, R)) (g₁ g₂ : C₀(β, E)) :
    prodSMul f (g₁ + g₂) = prodSMul f g₁ + prodSMul f g₂ := by ext; simp

/-- Elementary tensors commute with compatible scalar multiplication on the right factor. -/
theorem prodSMul_smul {S : Type*} [SMulZeroClass S E] [ContinuousConstSMul S E]
    [SMulCommClass R S E] (s : S) (f : C₀(α, R)) (g : C₀(β, E)) :
    prodSMul f (s • g) = s • prodSMul f g := by ext; simp [smul_comm]

/-- Elementary tensors associate with scalar multiplication on the left factor. -/
theorem smul_prodSMul {S : Type*} [SMulZeroClass S R] [ContinuousConstSMul S R]
    [SMulZeroClass S E] [ContinuousConstSMul S E] [IsScalarTower S R E]
    (s : S) (f : C₀(α, R)) (g : C₀(β, E)) :
    prodSMul (s • f) g = s • prodSMul f g := by ext; simp [smul_assoc]

/-- Reassociating `(α × β) × γ` to `α × (β × γ)` reassociates iterated elementary tensors. -/
theorem congrLeft_prodAssoc_prodSMul {γ : Type*} [TopologicalSpace γ]
    (f : C₀(α, R)) (g : C₀(β, R)) (h : C₀(γ, E)) :
    congrLeft R E (Homeomorph.prodAssoc α β γ) (prodSMul (prodSMul f g) h) =
      prodSMul f (prodSMul g h) := by ext ⟨x, y, z⟩; simp [Homeomorph.prodAssoc, mul_smul]

end BoundedSMul

/-- When scalar multiplication preserves norms, `‖prodSMul f g‖ = ‖f‖ * ‖g‖`. -/
@[simp] theorem norm_prodSMul {R E : Type*} [NormedRing R] [NormedAddCommGroup E] [Module R E]
    [NormSMulClass R E] (f : C₀(α, R)) (g : C₀(β, E)) : ‖prodSMul f g‖ = ‖f‖ * ‖g‖ := by
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

/-- Over a commutative seminormed ring, swapping `α × β` swaps elementary tensor factors. -/
theorem congrLeft_prodComm_prodSMul {R : Type*} [SeminormedCommRing R]
    (f : C₀(α, R)) (g : C₀(β, R)) :
    congrLeft R R (Homeomorph.prodComm α β) (prodSMul f g) = prodSMul g f := by
  ext ⟨y, x⟩; simp [mul_comm]

end ProdSMul

/-! ### Tensorial operators on discrete product spaces -/

section Discrete

variable {I I' J J' L S R E F G : Type*}
  [TopologicalSpace I] [DiscreteTopology I] [TopologicalSpace I'] [DiscreteTopology I']
  [TopologicalSpace J] [DiscreteTopology J] [TopologicalSpace J'] [DiscreteTopology J']
  [TopologicalSpace L] [DiscreteTopology L]

/-- On discrete index types, the elementary tensor of two coordinate vectors is a coordinate
vector. -/
@[simp] theorem prodSMul_single [SeminormedRing R] [SeminormedAddCommGroup E] [Module R E]
    [IsBoundedSMul R E] [DecidableEq I] [DecidableEq J] (i : I) (r : R) (j : J) (e : E) :
    prodSMul (single i r) (single j e) = single (i, j) (r • e) := by
  ext ⟨i', j'⟩; by_cases hi : i' = i <;> by_cases hj : j' = j <;> simp [hi, hj]

section Semiring

variable [Semiring S]
  [SeminormedAddCommGroup E] [Module S E] [ContinuousConstSMul S E]
  [SeminormedAddCommGroup F] [Module S F] [ContinuousConstSMul S F]
  [SeminormedAddCommGroup G] [Module S G] [ContinuousConstSMul S G]

/-- Currying `prodSMul f g` gives scalar multiples of `g` by the entries of `f`. -/
@[simp] theorem curryEquiv_prodSMul_apply [SeminormedRing R] [Module R E] [IsBoundedSMul R E]
    (f : C₀(I, R)) (g : C₀(J, E)) (i : I) :
    curryEquiv S E (prodSMul f g) i = f i • g := by ext; simp

variable (I) in
/-- **Contraction in the second variable**: a uniformly bounded `v : C₀(J, E) →L[S] F` acts on
each row of `f ∈ C₀(I × J, E)`, producing `C₀(I × J, E) →L[S] C₀(I, F)`. -/
noncomputable def contractSnd (v : C₀(J, E) →L[S] F) (hv : ∃ C, ∀ g, ‖v g‖ ≤ C * ‖g‖) :
    C₀(I × J, E) →L[S] C₀(I, F) :=
  compLeft (α := I) v hv ∘L
    (curryEquiv (I := I) (J := J) S E).toLinearIsometry.toContinuousLinearMap

/-- `contractSnd I v hv f` evaluates at `i` by applying `v` to the `i`-th row of `f`. -/
@[simp] theorem contractSnd_apply (v : C₀(J, E) →L[S] F) (hv : ∃ C, ∀ g, ‖v g‖ ≤ C * ‖g‖)
    (f : C₀(I × J, E)) (i : I) :
    contractSnd I v hv f i = v (curryEquiv S E f i) := by simp [contractSnd]

/-- A uniform bound for `v` is also a uniform bound for `contractSnd I v`. -/
theorem norm_contractSnd_apply_le (v : C₀(J, E) →L[S] F) {C : ℝ}
    (hC : ∀ g, ‖v g‖ ≤ C * ‖g‖) (f : C₀(I × J, E)) :
    ‖contractSnd I v ⟨C, hC⟩ f‖ ≤ C * ‖f‖ := by
  simpa [contractSnd] using norm_compLeft_apply_le v hC (curryEquiv S E f)

variable (I) in
/-- **Operator action on the second factor** `C₀(I × J, E) →L[S] C₀(I × J', F)` row by row. -/
noncomputable def sndMapCLM (v : C₀(J, E) →L[S] C₀(J', F)) (hv : ∃ C, ∀ g, ‖v g‖ ≤ C * ‖g‖) :
    C₀(I × J, E) →L[S] C₀(I × J', F) :=
  (curryEquiv (I := I) (J := J') S F).symm.toLinearIsometry.toContinuousLinearMap ∘L
    contractSnd I v hv

/-- `sndMapCLM I v hv f` applies `v` to the `i`-th row of `f`. -/
@[simp] theorem sndMapCLM_apply (v : C₀(J, E) →L[S] C₀(J', F)) (hv : ∃ C, ∀ g, ‖v g‖ ≤ C * ‖g‖)
    (f : C₀(I × J, E)) (i : I) (j' : J') :
    sndMapCLM I v hv f (i, j') = v (curryEquiv S E f i) j' := by simp [sndMapCLM]

/-- Currying `sndMapCLM I v hv f` gives `v` applied to each row of `f`. -/
@[simp] theorem curryEquiv_sndMapCLM_apply (v : C₀(J, E) →L[S] C₀(J', F))
    (hv : ∃ C, ∀ g, ‖v g‖ ≤ C * ‖g‖) (f : C₀(I × J, E)) (i : I) :
    curryEquiv S F (sndMapCLM I v hv f) i = v (curryEquiv S E f i) := by ext; simp

/-- A uniform bound for `v` is also a uniform bound for `sndMapCLM I v`. -/
theorem norm_sndMapCLM_apply_le (v : C₀(J, E) →L[S] C₀(J', F)) {C : ℝ}
    (hC : ∀ g, ‖v g‖ ≤ C * ‖g‖) (f : C₀(I × J, E)) :
    ‖sndMapCLM I v ⟨C, hC⟩ f‖ ≤ C * ‖f‖ := by
  simpa [sndMapCLM] using norm_contractSnd_apply_le v hC f

/-- `sndMapCLM` is itself uniformly bounded. -/
theorem exists_norm_sndMapCLM_apply_le (v : C₀(J, E) →L[S] C₀(J', F))
    (hv : ∃ C, ∀ g, ‖v g‖ ≤ C * ‖g‖) :
    ∃ C, ∀ f : C₀(I × J, E), ‖sndMapCLM I v hv f‖ ≤ C * ‖f‖ := by
  obtain ⟨C, hC⟩ := hv
  exact ⟨max C 0, norm_sndMapCLM_apply_le v fun g ↦
    (hC g).trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (norm_nonneg g))⟩

/-- The identity operator induces the identity on the second factor. -/
@[simp] theorem sndMapCLM_id (h : ∃ C, ∀ g : C₀(J, E), ‖ContinuousLinearMap.id S _ g‖ ≤ C * ‖g‖) :
    sndMapCLM I (ContinuousLinearMap.id S C₀(J, E)) h = ContinuousLinearMap.id S _ := by
  ext f ⟨i, j⟩; simp

/-- `sndMapCLM` respects operator composition. -/
theorem sndMapCLM_comp (w : C₀(J', F) →L[S] C₀(L, G)) (v : C₀(J, E) →L[S] C₀(J', F))
    (hw : ∃ C, ∀ g, ‖w g‖ ≤ C * ‖g‖) (hv : ∃ C, ∀ g, ‖v g‖ ≤ C * ‖g‖)
    (hwv : ∃ C, ∀ g, ‖w.comp v g‖ ≤ C * ‖g‖) :
    sndMapCLM I (w.comp v) hwv = (sndMapCLM I w hw).comp (sndMapCLM I v hv) := by
  ext f ⟨i, l⟩; simp

/-- On `single (i, j) e`, `sndMapCLM` acts on `single j e` in row `i` and vanishes elsewhere. -/
theorem sndMapCLM_single [DecidableEq I] [DecidableEq J]
    (v : C₀(J, E) →L[S] C₀(J', F)) (hv : ∃ C, ∀ g, ‖v g‖ ≤ C * ‖g‖) (i : I) (j : J) (e : E) :
    sndMapCLM I v hv (single (i, j) e) = (curryEquiv S F).symm (single i (v (single j e))) := by
  ext ⟨i', j'⟩; by_cases hi : i' = i <;> simp [hi]

variable (J) in
/-- **Operator action on the first factor** `C₀(I × J, E) →L[S] C₀(I' × J, F)` column by column. -/
noncomputable def fstMapCLM (u : C₀(I, E) →L[S] C₀(I', F)) (hu : ∃ C, ∀ f, ‖u f‖ ≤ C * ‖f‖) :
    C₀(I × J, E) →L[S] C₀(I' × J, F) :=
  (congrLeft S F (Homeomorph.prodComm J I')).toLinearIsometry.toContinuousLinearMap ∘L
    sndMapCLM J u hu ∘L
      (congrLeft S E (Homeomorph.prodComm I J)).toLinearIsometry.toContinuousLinearMap

/-- `fstMapCLM J u hu f` applies `u` to the `j`-th column of `f`. -/
@[simp] theorem fstMapCLM_apply (u : C₀(I, E) →L[S] C₀(I', F)) (hu : ∃ C, ∀ f, ‖u f‖ ≤ C * ‖f‖)
    (f : C₀(I × J, E)) (i' : I') (j : J) :
    fstMapCLM J u hu f (i', j) =
      u (curryEquiv S E (congrLeft S E (Homeomorph.prodComm I J) f) j) i' := by simp [fstMapCLM]

/-- A uniform bound for `u` is also a uniform bound for `fstMapCLM J u`. -/
theorem norm_fstMapCLM_apply_le (u : C₀(I, E) →L[S] C₀(I', F)) {C : ℝ}
    (hC : ∀ f, ‖u f‖ ≤ C * ‖f‖) (f : C₀(I × J, E)) :
    ‖fstMapCLM J u ⟨C, hC⟩ f‖ ≤ C * ‖f‖ := by
  simpa [fstMapCLM] using norm_sndMapCLM_apply_le u hC (congrLeft S E (Homeomorph.prodComm I J) f)

/-- `fstMapCLM` is itself uniformly bounded. -/
theorem exists_norm_fstMapCLM_apply_le (u : C₀(I, E) →L[S] C₀(I', F))
    (hu : ∃ C, ∀ f, ‖u f‖ ≤ C * ‖f‖) :
    ∃ C, ∀ f : C₀(I × J, E), ‖fstMapCLM J u hu f‖ ≤ C * ‖f‖ := by
  obtain ⟨C, hC⟩ := hu
  exact ⟨max C 0, norm_fstMapCLM_apply_le u fun g ↦
    (hC g).trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (norm_nonneg g))⟩

/-- The identity operator induces the identity on the first factor. -/
@[simp] theorem fstMapCLM_id (h : ∃ C, ∀ f : C₀(I, E), ‖ContinuousLinearMap.id S _ f‖ ≤ C * ‖f‖) :
    fstMapCLM J (ContinuousLinearMap.id S C₀(I, E)) h = ContinuousLinearMap.id S _ := by
  ext f ⟨i, j⟩; simp

/-- `fstMapCLM` respects operator composition. -/
theorem fstMapCLM_comp (w : C₀(I', F) →L[S] C₀(L, G)) (u : C₀(I, E) →L[S] C₀(I', F))
    (hw : ∃ C, ∀ f, ‖w f‖ ≤ C * ‖f‖) (hu : ∃ C, ∀ f, ‖u f‖ ≤ C * ‖f‖)
    (hwu : ∃ C, ∀ f, ‖w.comp u f‖ ≤ C * ‖f‖) :
    fstMapCLM J (w.comp u) hwu = (fstMapCLM J w hw).comp (fstMapCLM J u hu) := by
  ext f ⟨l, j⟩
  have hswap : congrLeft S F (Homeomorph.prodComm I' J)
      (congrLeft S F (Homeomorph.prodComm J I')
        (sndMapCLM J u hu (congrLeft S E (Homeomorph.prodComm I J) f))) =
      sndMapCLM J u hu (congrLeft S E (Homeomorph.prodComm I J) f) := by ext ⟨j', i'⟩; simp
  simp [fstMapCLM, hswap]

/-- `sndMapCLM` depends only on the pointwise action of `v`. -/
theorem sndMapCLM_congr_apply {S₂ : Type*} [Semiring S₂]
    [Module S₂ E] [ContinuousConstSMul S₂ E] [Module S₂ F] [ContinuousConstSMul S₂ F]
    (v₁ : C₀(J, E) →L[S] C₀(J', F)) (hv₁ : ∃ C, ∀ g, ‖v₁ g‖ ≤ C * ‖g‖)
    (v₂ : C₀(J, E) →L[S₂] C₀(J', F)) (hv₂ : ∃ C, ∀ g, ‖v₂ g‖ ≤ C * ‖g‖)
    (hv : ∀ g, v₁ g = v₂ g) (f : C₀(I × J, E)) :
    sndMapCLM I v₁ hv₁ f = sndMapCLM I v₂ hv₂ f := by
  ext ⟨i, j'⟩
  rw [sndMapCLM_apply, sndMapCLM_apply,
    show curryEquiv S E f i = curryEquiv S₂ E f i by ext; simp, hv]

/-- `fstMapCLM` depends only on the pointwise action of `u`. -/
theorem fstMapCLM_congr_apply {S₂ : Type*} [Semiring S₂]
    [Module S₂ E] [ContinuousConstSMul S₂ E] [Module S₂ F] [ContinuousConstSMul S₂ F]
    (u₁ : C₀(I, E) →L[S] C₀(I', F)) (hu₁ : ∃ C, ∀ f, ‖u₁ f‖ ≤ C * ‖f‖)
    (u₂ : C₀(I, E) →L[S₂] C₀(I', F)) (hu₂ : ∃ C, ∀ f, ‖u₂ f‖ ≤ C * ‖f‖)
    (hu : ∀ g, u₁ g = u₂ g) (f : C₀(I × J, E)) :
    fstMapCLM J u₁ hu₁ f = fstMapCLM J u₂ hu₂ f := by
  ext ⟨i', j⟩
  rw [fstMapCLM_apply, fstMapCLM_apply,
    show curryEquiv S E (congrLeft S E (Homeomorph.prodComm I J) f) j =
      curryEquiv S₂ E (congrLeft S₂ E (Homeomorph.prodComm I J) f) j by ext; simp, hu]

/-- **Product of two operators** `C₀(I × J, E) →L[S] C₀(I' × J', G)`. -/
noncomputable def prodMapCLM (u : C₀(I, E) →L[S] C₀(I', F)) (hu : ∃ C, ∀ f, ‖u f‖ ≤ C * ‖f‖)
    (v : C₀(J, F) →L[S] C₀(J', G)) (hv : ∃ C, ∀ g, ‖v g‖ ≤ C * ‖g‖) :
    C₀(I × J, E) →L[S] C₀(I' × J', G) :=
  sndMapCLM I' v hv ∘L fstMapCLM J u hu

/-- `prodMapCLM` factors as `sndMapCLM` after `fstMapCLM`. -/
theorem prodMapCLM_def (u : C₀(I, E) →L[S] C₀(I', F)) (hu : ∃ C, ∀ f, ‖u f‖ ≤ C * ‖f‖)
    (v : C₀(J, F) →L[S] C₀(J', G)) (hv : ∃ C, ∀ g, ‖v g‖ ≤ C * ‖g‖) :
    prodMapCLM u hu v hv = sndMapCLM I' v hv ∘L fstMapCLM J u hu := (rfl)

/-- A product of nonnegative bounds for `u` and `v` bounds `prodMapCLM u _ v _`. -/
theorem norm_prodMapCLM_apply_le (u : C₀(I, E) →L[S] C₀(I', F)) (v : C₀(J, F) →L[S] C₀(J', G))
    {C₁ C₂ : ℝ} (hC₂ : 0 ≤ C₂) (hu : ∀ f, ‖u f‖ ≤ C₁ * ‖f‖) (hv : ∀ g, ‖v g‖ ≤ C₂ * ‖g‖)
    (f : C₀(I × J, E)) : ‖prodMapCLM u ⟨C₁, hu⟩ v ⟨C₂, hv⟩ f‖ ≤ C₂ * C₁ * ‖f‖ := by
  rw [prodMapCLM, ContinuousLinearMap.comp_apply, mul_assoc]
  exact (norm_sndMapCLM_apply_le v hv _).trans
    (mul_le_mul_of_nonneg_left (norm_fstMapCLM_apply_le u hu f) hC₂)

/-- `sndMapCLM` preserves intertwining with bounded coefficient maps. -/
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
  ext ⟨i, j'⟩; simpa [curryEquiv_compLeft] using congr($hinter (curryEquiv S E f i) j')

/-- `fstMapCLM` preserves intertwining with bounded coefficient maps. -/
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
    LinearIsometryEquiv.coe_toLinearIsometry, ← congrLeft_compLeft,
    compLeft_sndMapCLM w₁ hw₁ w₂ hw₂ u hu u' hu' hinter]

end Semiring

section CommRing

variable {R : Type*} [SeminormedCommRing R]

/-- Over a commutative seminormed ring, `sndMapCLM` acts on the second tensor factor. -/
@[simp] theorem sndMapCLM_prodSMul (v : C₀(J, R) →L[R] C₀(J', R)) (hv : ∃ C, ∀ g, ‖v g‖ ≤ C * ‖g‖)
    (f : C₀(I, R)) (g : C₀(J, R)) :
    sndMapCLM I v hv (prodSMul f g) = prodSMul f (v g) := by
  ext ⟨i, j'⟩; simp [curryEquiv_prodSMul_apply (S := R)]

/-- Over a commutative seminormed ring, `fstMapCLM` acts on the first tensor factor. -/
@[simp] theorem fstMapCLM_prodSMul (u : C₀(I, R) →L[R] C₀(I', R)) (hu : ∃ C, ∀ f, ‖u f‖ ≤ C * ‖f‖)
    (f : C₀(I, R)) (g : C₀(J, R)) :
    fstMapCLM J u hu (prodSMul f g) = prodSMul (u f) g := by
  ext ⟨i', j⟩; simp [congrLeft_prodComm_prodSMul, curryEquiv_prodSMul_apply (S := R), mul_comm]

/-- Over a commutative seminormed ring, `prodMapCLM` acts factorwise on elementary tensors. -/
@[simp] theorem prodMapCLM_prodSMul (u : C₀(I, R) →L[R] C₀(I', R)) (hu : ∃ C, ∀ f, ‖u f‖ ≤ C * ‖f‖)
    (v : C₀(J, R) →L[R] C₀(J', R)) (hv : ∃ C, ∀ g, ‖v g‖ ≤ C * ‖g‖)
    (f : C₀(I, R)) (g : C₀(J, R)) :
    prodMapCLM u hu v hv (prodSMul f g) = prodSMul (u f) (v g) := by simp [prodMapCLM]

end CommRing

/-! ### Bilinear pairing of continuous linear functionals -/

section ProdPairing

variable {K : Type*} [NontriviallyNormedField K]

/-- **Product of two continuous linear functionals** `prodPairing u v ∈ C₀(I × J, K)*` over any
nontrivially normed field `K`, obtained by applying `v` along rows and `u` across rows. -/
noncomputable def prodPairing (u : C₀(I, K) →L[K] K) (v : C₀(J, K) →L[K] K) :
    C₀(I × J, K) →L[K] K :=
  u ∘L contractSnd I v ⟨‖v‖, v.le_opNorm⟩

/-- `prodPairing u v` applies `v` along each row and then `u` to the resulting family. -/
theorem prodPairing_apply (u : C₀(I, K) →L[K] K) (v : C₀(J, K) →L[K] K) (f : C₀(I × J, K)) :
    prodPairing u v f = u (contractSnd I v ⟨‖v‖, v.le_opNorm⟩ f) := (rfl)

/-- Pairing with the zero functional on the left gives zero. -/
@[simp] theorem prodPairing_zero_left (v : C₀(J, K) →L[K] K) :
    prodPairing (0 : C₀(I, K) →L[K] K) v = 0 := by ext; simp [prodPairing_apply]

/-- Pairing with the zero functional on the right gives zero. -/
@[simp] theorem prodPairing_zero_right (u : C₀(I, K) →L[K] K) :
    prodPairing u (0 : C₀(J, K) →L[K] K) = 0 := by
  ext f
  simp [prodPairing_apply, show contractSnd I (0 : C₀(J, K) →L[K] K) ⟨‖(0 : C₀(J, K) →L[K] K)‖,
    ContinuousLinearMap.le_opNorm 0⟩ f = 0 by ext; simp]

/-- `prodPairing` is additive in the left functional. -/
theorem prodPairing_add_left (u₁ u₂ : C₀(I, K) →L[K] K) (v : C₀(J, K) →L[K] K) :
    prodPairing (u₁ + u₂) v = prodPairing u₁ v + prodPairing u₂ v := by ext; rfl

/-- `prodPairing` is additive in the right functional. -/
theorem prodPairing_add_right (u : C₀(I, K) →L[K] K) (v₁ v₂ : C₀(J, K) →L[K] K) :
    prodPairing u (v₁ + v₂) = prodPairing u v₁ + prodPairing u v₂ := by
  ext f
  rw [prodPairing_apply, show contractSnd I (v₁ + v₂) ⟨‖v₁ + v₂‖, (v₁ + v₂).le_opNorm⟩ f =
    contractSnd I v₁ ⟨‖v₁‖, v₁.le_opNorm⟩ f + contractSnd I v₂ ⟨‖v₂‖, v₂.le_opNorm⟩ f by ext; simp,
    map_add]; rfl

/-- `prodPairing` is `K`-linear in the left functional. -/
theorem prodPairing_smul_left (c : K) (u : C₀(I, K) →L[K] K) (v : C₀(J, K) →L[K] K) :
    prodPairing (c • u) v = c • prodPairing u v := by ext; rfl

/-- `prodPairing` is `K`-linear in the right functional. -/
theorem prodPairing_smul_right (c : K) (u : C₀(I, K) →L[K] K) (v : C₀(J, K) →L[K] K) :
    prodPairing u (c • v) = c • prodPairing u v := by
  ext f
  rw [prodPairing_apply, show contractSnd I (c • v) ⟨‖c • v‖, (c • v).le_opNorm⟩ f =
    c • contractSnd I v ⟨‖v‖, v.le_opNorm⟩ f by ext; simp, map_smul]; rfl

/-- `prodPairing` commutes with negation in the left functional. -/
@[simp] theorem prodPairing_neg_left (u : C₀(I, K) →L[K] K) (v : C₀(J, K) →L[K] K) :
    prodPairing (-u) v = -prodPairing u v := by ext; rfl

/-- `prodPairing` commutes with negation in the right functional. -/
@[simp] theorem prodPairing_neg_right (u : C₀(I, K) →L[K] K) (v : C₀(J, K) →L[K] K) :
    prodPairing u (-v) = -prodPairing u v := by
  ext f
  rw [prodPairing_apply, show contractSnd I (-v) ⟨‖-v‖, (-v).le_opNorm⟩ f =
    -contractSnd I v ⟨‖v‖, v.le_opNorm⟩ f by ext; simp, map_neg]; rfl

/-- On an elementary tensor `prodSMul f g`, the product functional evaluates to `u f * v g`. -/
@[simp] theorem prodPairing_prodSMul (u : C₀(I, K) →L[K] K) (v : C₀(J, K) →L[K] K)
    (f : C₀(I, K)) (g : C₀(J, K)) :
    prodPairing u v (prodSMul f g) = u f * v g := by
  rw [prodPairing_apply, show contractSnd I v ⟨‖v‖, v.le_opNorm⟩ (prodSMul f g) = v g • f by
    ext; simp [mul_comm], map_smul, smul_eq_mul, mul_comm]

/-- On `single (i, j) a`, `prodPairing u v` evaluates to `a * (u (single i 1) * v (single j 1))`. -/
theorem prodPairing_single [DecidableEq I] [DecidableEq J]
    (u : C₀(I, K) →L[K] K) (v : C₀(J, K) →L[K] K) (i : I) (j : J) (a : K) :
    prodPairing u v (single (i, j) a) = a * (u (single i 1) * v (single j 1)) := by
  rw [show single (i, j) a = a • prodSMul (single i (1 : K)) (single j (1 : K)) by
    simp [← single_smul], map_smul, prodPairing_prodSMul, smul_eq_mul]

/-- **Exact norm of the product functional**: `‖prodPairing u v‖ = ‖u‖ * ‖v‖`. -/
@[simp] theorem norm_prodPairing (u : C₀(I, K) →L[K] K) (v : C₀(J, K) →L[K] K) :
    ‖prodPairing u v‖ = ‖u‖ * ‖v‖ := by
  have hp : 0 ≤ ‖prodPairing u v‖ := (prodPairing u v).opNorm_nonneg
  have hu0 : 0 ≤ ‖u‖ := u.opNorm_nonneg
  refine le_antisymm ((prodPairing u v).opNorm_le_bound (mul_nonneg hu0 v.opNorm_nonneg) fun f ↦ by
    rw [prodPairing_apply, mul_assoc]
    exact (u.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (norm_contractSnd_apply_le v v.le_opNorm f) hu0)) ?_
  rcases hu0.eq_or_lt with hu | hu
  · simpa [← hu] using hp
  · rw [← le_div_iff₀' hu]
    refine v.opNorm_le_bound (div_nonneg hp hu.le) fun g ↦ ?_
    rw [div_mul_eq_mul_div, le_div_iff₀ hu, mul_comm ‖v g‖ ‖u‖]
    rcases (norm_nonneg (v g)).eq_or_lt with hvg | hvg
    · simpa [← hvg] using mul_nonneg hp (norm_nonneg g)
    · rw [← le_div_iff₀ hvg]
      refine u.opNorm_le_bound (div_nonneg (mul_nonneg hp (norm_nonneg g)) hvg.le) fun f ↦ ?_
      rw [div_mul_eq_mul_div, le_div_iff₀ hvg, ← norm_mul, ← prodPairing_prodSMul]
      exact ((prodPairing u v).le_opNorm _).trans_eq (by rw [norm_prodSMul]; ring)

/-- **Fubini symmetry for `prodPairing`** along `Homeomorph.prodComm`. -/
theorem prodPairing_comp_congrLeft_prodComm (u : C₀(I, K) →L[K] K) (v : C₀(J, K) →L[K] K) :
    prodPairing v u ∘L
        (congrLeft K K (Homeomorph.prodComm I J)).toLinearIsometry.toContinuousLinearMap =
      prodPairing u v := by
  classical
  refine continuousLinearMap_ext_single_one fun ⟨i, j⟩ ↦ ?_
  simp [prodPairing_single, mul_comm]

/-- Pointwise form of Fubini symmetry for `prodPairing`. -/
theorem prodPairing_congrLeft_prodComm (u : C₀(I, K) →L[K] K) (v : C₀(J, K) →L[K] K)
    (f : C₀(I × J, K)) :
    prodPairing v u (congrLeft K K (Homeomorph.prodComm I J) f) = prodPairing u v f :=
  congr($(prodPairing_comp_congrLeft_prodComm u v) f)

/-- **Naturality of `prodPairing`** with respect to `prodMapCLM`. -/
theorem prodPairing_comp_prodMapCLM (u : C₀(I', K) →L[K] K) (v : C₀(J', K) →L[K] K)
    (T₁ : C₀(I, K) →L[K] C₀(I', K)) (hT₁ : ∃ C, ∀ f, ‖T₁ f‖ ≤ C * ‖f‖)
    (T₂ : C₀(J, K) →L[K] C₀(J', K)) (hT₂ : ∃ C, ∀ g, ‖T₂ g‖ ≤ C * ‖g‖) :
    prodPairing u v ∘L prodMapCLM T₁ hT₁ T₂ hT₂ = prodPairing (u ∘L T₁) (v ∘L T₂) := by
  classical
  refine continuousLinearMap_ext_single_one fun ⟨i, j⟩ ↦ ?_
  have h1 : single (i, j) (1 : K) = prodSMul (single i (1 : K)) (single j (1 : K)) := by simp
  rw [h1, ContinuousLinearMap.comp_apply, prodMapCLM_prodSMul, prodPairing_prodSMul,
    prodPairing_prodSMul]; rfl

/-- Naturality of `prodPairing` in the first factor. -/
theorem prodPairing_comp_fstMapCLM (u : C₀(I', K) →L[K] K) (v : C₀(J, K) →L[K] K)
    (T₁ : C₀(I, K) →L[K] C₀(I', K)) (hT₁ : ∃ C, ∀ f, ‖T₁ f‖ ≤ C * ‖f‖) :
    prodPairing u v ∘L fstMapCLM J T₁ hT₁ = prodPairing (u ∘L T₁) v := by
  simpa [prodMapCLM, sndMapCLM_id] using prodPairing_comp_prodMapCLM u v T₁ hT₁
    (ContinuousLinearMap.id K C₀(J, K)) ⟨1, fun g ↦ by simp⟩

/-- Naturality of `prodPairing` in the second factor. -/
theorem prodPairing_comp_sndMapCLM (u : C₀(I, K) →L[K] K) (v : C₀(J', K) →L[K] K)
    (T₂ : C₀(J, K) →L[K] C₀(J', K)) (hT₂ : ∃ C, ∀ g, ‖T₂ g‖ ≤ C * ‖g‖) :
    prodPairing u v ∘L sndMapCLM I T₂ hT₂ = prodPairing u (v ∘L T₂) := by
  simpa [prodMapCLM, fstMapCLM_id] using prodPairing_comp_prodMapCLM u v
    (ContinuousLinearMap.id K C₀(I, K)) ⟨1, fun f ↦ by simp⟩ T₂ hT₂

/-- **Associativity of `prodPairing`** along `Homeomorph.prodAssoc`. -/
theorem prodPairing_comp_congrLeft_prodAssoc
    (u : C₀(I, K) →L[K] K) (v : C₀(J, K) →L[K] K) (w : C₀(L, K) →L[K] K) :
    prodPairing u (prodPairing v w) ∘L
        (congrLeft K K (Homeomorph.prodAssoc I J L)).toLinearIsometry.toContinuousLinearMap =
      prodPairing (prodPairing u v) w := by
  classical
  refine continuousLinearMap_ext_single_one fun ⟨⟨i, j⟩, l⟩ ↦ ?_
  simp [Homeomorph.prodAssoc, prodPairing_single, mul_assoc]

end ProdPairing

end Discrete

end ZeroAtInftyContinuousMap
