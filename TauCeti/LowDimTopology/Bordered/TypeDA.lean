/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Bordered.TypeA

/-!
# Type `DA` bimodules and their box tensor products with type `D` structures

A three-manifold with two boundary components, such as a mapping cylinder, has a type `DA`
bimodule `^A M_B` in bordered Heegaard Floer homology: a type `D` structure over the algebra `A` of
one boundary which is at the same time an `A∞` module over the algebra `B` of the other. Gluing it
to a manifold with a type `D` structure `^B N` gives the box tensor product `M ⊠ N`, a type `D`
structure over `A`. This is how bimodules act on type `D` structures; the associativity of the
box tensor product compares `P ⊠ (M ⊠ N)` with `(P ⊠ M) ⊠ N` for a type `A` module `P` over `A`.

Over a ring of characteristic two, a type `DA` bimodule has structure maps
`δ¹_{n+1} : M ⊗ B^{⊗ n} → A ⊗ M` for every `n ≥ 0`. In a basis of generators `y : Y`, each with a
left idempotent of `A` and a right idempotent of `B`, the map `δ¹_{n+1}` is a matrix of
coefficients `δ_{n+1}(b₁, …, bₙ) : Matrix Y Y A`, multilinear in the inputs `bᵢ`
(`TauCeti.TypeDABimodule`). The structure relation of length `n` is

`d δ_{n+1}(b) + ∑_{i + j = n} δ_{i+1}(b₁, …, bᵢ) δ_{j+1}(bᵢ₊₁, …, bₙ)`
`  + ∑_l δ_{n+1}(b₁, …, d bₗ, …, bₙ) + ∑_l δ_n(b₁, …, bₗ bₗ₊₁, …, bₙ) = 0`,

the differential `d` of `A` acting on matrices entrywise. For `n = 0` this is the type `D`
structure equation `d δ₁ + δ₁ δ₁ = 0`, and when `A` is the ground ring these are the relations of
an `A∞` module over `B`.

* **The induced module.** The row vectors `φ : Y → A`, a model of `A ⊠ M`, form an ungraded `A∞`
  right module over `B` (`TauCeti.TypeDABimodule.inducedModule`), with
  `m₁(φ) = d φ + φ ⬝ δ₁` and `m_{n+1}(φ, b₁, …, bₙ) = φ ⬝ δ_{n+1}(b₁, …, bₙ)`. Its `A∞` relation
  of length `n` is the structure relation of length `n` applied to `φ`: the terms `d φ ⬝ δ_{n+1}`
  coming from the two ends of the composite terms cancel in characteristic two, by the Leibniz
  rule of `d`.
* **The box tensor product.** For a type `D` structure `N` over `B` with generators `X` and
  coefficient matrix `ε`, the box tensor product `M ⊠ N` has the generators `y ⊗ x` with matching
  idempotents, `idemRight y = idem x`, and the structure map
  `δ¹(y ⊗ x) = ∑_n (δ¹_{n+1} ⊗ 1)(y ⊗ δⁿ(x))`. Its coefficient from `y ⊗ x` to `y' ⊗ z`
  (`TauCeti.TypeDABimodule.boxCoeff`) is the sum, over the paths `x = x₀ → ⋯ → xₙ = z` in `X`, of
  the `(y, y')` entry of `δ_{n+1}(ε x₀ x₁, …, ε xₙ₋₁ xₙ)`. The sum is finite when `N` is bounded
  (`TauCeti.TypeDStructure.IsBounded`) or when `δ_{n+1}` vanishes for large `n`.

The structure equation of `M ⊠ N` comes from the box tensor product of the induced module with
`N` (`TauCeti.TypeDStructure.typeABoxDifferential`), which squares to zero under either
boundedness hypothesis: on row vectors `Φ : X → Y → A` that differential is `d Φ + Φ ⬝ C`, with
`C` the coefficient matrix of `M ⊠ N`, and its square is `Φ ⬝ (d C + C C)`. So the coefficients
satisfy `d C + C C = 0` on all pairs `y ⊗ x`
(`TauCeti.TypeDABimodule.map_boxCoeff_add_boxCoeff_mul_boxCoeff`).
The pairs with mismatched idempotents vanish in the tensor product over the idempotents of `B`;
since `δ¹` respects the right idempotents and those of `B` are orthogonal, no coefficient leads from
a matched pair to a mismatched one (`TauCeti.TypeDABimodule.boxCoeff_eq_zero_of_ne`), and the
restriction of `C` to the matched pairs is the coefficient matrix of a type `D` structure
(`TauCeti.TypeDABimodule.boxTensor`).

## Main definitions

* `TauCeti.TypeDABimodule`: a type `DA` bimodule, given by its generators, their left and right
  idempotents and its coefficient matrices.
* `TauCeti.TypeDABimodule.inducedModule`: the `A∞` right module `A ⊠ M` over `B`.
* `TauCeti.TypeDABimodule.boxCoeff`: the coefficients of the box tensor product with a type `D`
  structure.
* `TauCeti.TypeDABimodule.boxTensor`: the box tensor product `M ⊠ N`, a type `D` structure over
  `A`.

## Main results

* `TauCeti.TypeDABimodule.typeABoxDifferential_inducedModule_apply`: the box tensor differential
  of the induced module with `N` is `Φ ↦ d Φ + Φ ⬝ C`.
* `TauCeti.TypeDABimodule.map_boxCoeff_add_boxCoeff_mul_boxCoeff`: the structure equation
  `d C + C C = 0` on all pairs of generators.
* `TauCeti.TypeDABimodule.boxCoeff_eq_zero_of_ne`: no coefficient leads from a pair with matching
  idempotents to a pair without.
* `TauCeti.TypeDABimodule.boxCoeff_eq_sum_of_coeff_eq_zero` and
  `TauCeti.TypeDABimodule.boxCoeff_eq_sum_lift_iteratedCoeff`: the coefficients as finite sums,
  over the paths of length less than `K` when `δ_{n+1}` vanishes for `n ≥ K`, and as
  `∑_{n < K} δ_{n+1}(δⁿ(x))` when the iterates `δⁿ` of `N` vanish for `n ≥ K`
  (`TauCeti.TypeDABimodule.pathCoeff_def`).
* `TauCeti.TypeDABimodule.boxCoeff_eq_add_of_coeff_eq_zero`: for a bimodule with `δ_{n+1} = 0`
  for `n ≥ 2`, `δ¹(y ⊗ x) = δ¹₁(y) ⊗ x + ∑_z δ¹₂(y, ε x z) ⊗ z`.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bimodules in bordered Heegaard Floer homology*,
  Geom. Topol. **19** (2015), 525–724, [arXiv:1003.0598](https://arxiv.org/abs/1003.0598), §2.2
  (type `DA` structures and their structure relation) and §2.3 (the box tensor product of a type
  `DA` structure with a type `D` structure, and its boundedness hypotheses).
* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer.
  Math. Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687),
  Chapter 2 (type `D` structures, `A∞` modules and the box tensor product over `𝔽₂`).
-/

public section

open Finset MulOpposite

namespace TauCeti

variable {R A B : Type*} [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]

/-! ### The structure relation -/

section Relation

variable {Y : Type*}
  (δ : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => B) (Matrix Y Y A))

/-- The **composite terms** of the type `DA` structure relation of length `n`:
`∑_{i + j = n} δ_{i+1}(b₁, …, bᵢ) δ_{j+1}(bᵢ₊₁, …, bₙ)`, where `δ i` is `δ_{i+1}`. -/
noncomputable def typeDAStasheffComp [Fintype Y] (n : ℕ) (b : Fin n → B) : Matrix Y Y A :=
  ∑ k : Fin (n + 1), δ k (fun l => b ⟨l, by have := l.isLt; have := k.isLt; omega⟩) *
    δ (n - k) (fun l => b ⟨k + l, by have := l.isLt; omega⟩)

theorem typeDAStasheffComp_def [Fintype Y] (n : ℕ) (b : Fin n → B) :
    typeDAStasheffComp δ n b =
      ∑ k : Fin (n + 1), δ k (fun l => b ⟨l, by have := l.isLt; have := k.isLt; omega⟩) *
        δ (n - k) (fun l => b ⟨k + l, by have := l.isLt; omega⟩) :=
  (rfl)

/-- The **differential terms** of the type `DA` structure relation of length `n`:
`∑_l δ_{n+1}(b₁, …, d bₗ, …, bₙ)`. -/
noncomputable def typeDAStasheffDiff (dB : B →ₗ[R] B) (n : ℕ) (b : Fin n → B) : Matrix Y Y A :=
  ∑ l : Fin n, δ n (Function.update b l (dB (b l)))

theorem typeDAStasheffDiff_def (dB : B →ₗ[R] B) (n : ℕ) (b : Fin n → B) :
    typeDAStasheffDiff δ dB n b = ∑ l : Fin n, δ n (Function.update b l (dB (b l))) :=
  (rfl)

/-- The **product terms** of the type `DA` structure relation of length `n`:
`∑_l δ_n(b₁, …, bₗ bₗ₊₁, …, bₙ)`, over the `n - 1` adjacent pairs. -/
noncomputable def typeDAStasheffMul : (n : ℕ) → (Fin n → B) → Matrix Y Y A
  | 0, _ => 0
  | n + 1, b => ∑ l : Fin n, δ n (Fin.contractNth l.castSucc (· * ·) b)

@[simp]
theorem typeDAStasheffMul_zero (b : Fin 0 → B) : typeDAStasheffMul δ 0 b = 0 :=
  (rfl)

theorem typeDAStasheffMul_succ (n : ℕ) (b : Fin (n + 1) → B) :
    typeDAStasheffMul δ (n + 1) b = ∑ l : Fin n, δ n (Fin.contractNth l.castSucc (· * ·) b) :=
  (rfl)

end Relation

variable (dA : A →ₗ[R] A) (dB : B →ₗ[R] B) {S T : Type*} (ιA : S → A) (ιB : T → B)
  (Y : Type*) [Fintype Y]

/-- A **type `DA` bimodule** `^A M_B` over the differential algebras `(A, dA)` and `(B, dB)`, with
idempotents `ιA` and `ιB`, in a basis of generators `Y`. Each generator `y` lies in the summand
`ιA (idemLeft y) * M * ιB (idemRight y)`, and the structure map `δ¹_{n+1}` sends `y ⊗ b₁ ⊗ ⋯ ⊗ bₙ`
to `∑ y', coeff n b y y' ⊗ y'`. The coefficients lie in the summands of the left idempotents, and
`δ¹` respects the right idempotents: `δ¹₁` keeps them, and the coefficient of `y'` in
`δ¹_{n+1}(y, b₁, …, bₙ)` only sees `bₙ * ιB (idemRight y')`. The inputs are balanced over the
idempotents of `B`: the coefficient from `y` only sees `ιB (idemRight y) * b₁`, and
`δ¹_{n+1}(…, bₗ * ιB t, bₗ₊₁, …) = δ¹_{n+1}(…, bₗ, ιB t * bₗ₊₁, …)`, so `δ¹_{n+1}` is defined on
`M ⊗ B ⊗ ⋯ ⊗ B` with the tensor products taken over the idempotents. The structure relation of
length `n` is `d δ_{n+1}(b) + TauCeti.typeDAStasheffComp + TauCeti.typeDAStasheffDiff +
TauCeti.typeDAStasheffMul = 0`, with no signs: over a ring of characteristic two these are the
relations of Lipshitz, Ozsváth and Thurston, and no characteristic is imposed by the definition
itself. -/
@[ext]
structure TypeDABimodule where
  /-- The idempotent of `A` of each generator. -/
  idemLeft : Y → S
  /-- The idempotent of `B` of each generator. -/
  idemRight : Y → T
  /-- The coefficient matrices: `δ¹_{n+1}(y, b₁, …, bₙ) = ∑ y', coeff n b y y' ⊗ y'`. -/
  coeff : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => B) (Matrix Y Y A)
  /-- The coefficients from `y` lie in the summand of the idempotent of `y` on the left. -/
  idem_mul_coeff (n : ℕ) (b : Fin n → B) (y y' : Y) :
    ιA (idemLeft y) * coeff n b y y' = coeff n b y y'
  /-- The coefficients to `y'` lie in the summand of the idempotent of `y'` on the right. -/
  coeff_mul_idem (n : ℕ) (b : Fin n → B) (y y' : Y) :
    coeff n b y y' * ιA (idemLeft y') = coeff n b y y'
  /-- The map `δ¹₁` keeps the idempotents of `B`. -/
  coeff_zero_eq_zero_of_ne (b : Fin 0 → B) {y y' : Y} (h : idemRight y ≠ idemRight y') :
    coeff 0 b y y' = 0
  /-- The coefficient of `y'` in `δ¹_{n+2}(y, b₁, …, bₙ₊₁)` only depends on
  `bₙ₊₁ * ιB (idemRight y')`. -/
  coeff_succ_update_mul_idem (n : ℕ) (b : Fin (n + 1) → B) (y y' : Y) :
    coeff (n + 1) (Function.update b (Fin.last n) (b (Fin.last n) * ιB (idemRight y'))) y y' =
      coeff (n + 1) b y y'
  /-- The coefficient from `y` in `δ¹_{n+2}(y, b₁, …, bₙ₊₁)` only depends on
  `ιB (idemRight y) * b₁`. -/
  coeff_succ_update_idem_mul (n : ℕ) (b : Fin (n + 1) → B) (y y' : Y) :
    coeff (n + 1) (Function.update b 0 (ιB (idemRight y) * b 0)) y y' = coeff (n + 1) b y y'
  /-- Adjacent inputs are balanced over the idempotents of `B`:
  `δ¹_{n+3}(…, bₗ * ιB t, bₗ₊₁, …) = δ¹_{n+3}(…, bₗ, ιB t * bₗ₊₁, …)`. -/
  coeff_update_mul_idem_eq_update_idem_mul (n : ℕ) (b : Fin (n + 2) → B) (l : Fin (n + 1))
      (t : T) :
    coeff (n + 2) (Function.update b l.castSucc (b l.castSucc * ιB t)) =
      coeff (n + 2) (Function.update b l.succ (ιB t * b l.succ))
  /-- The structure relation of length `n`. -/
  stasheff (n : ℕ) (b : Fin n → B) :
    (coeff n b).map dA + typeDAStasheffComp coeff n b + typeDAStasheffDiff coeff dB n b +
      typeDAStasheffMul coeff n b = 0

namespace TypeDABimodule

variable {dA dB ιA ιB Y}

/-! ### The induced `A∞` module -/

section Induced

variable (dA) in
/-- The differential term of the induced operations: `d` on `m₁`, and nothing on the higher
operations. -/
private noncomputable def diffAct :
    (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => B) ((Y → A) →ₗ[R] Y → A)
  | 0 => MultilinearMap.constOfIsEmpty (RingHom.id R) _
    (LinearMap.pi fun y => dA ∘ₗ LinearMap.proj y)
  | _ + 1 => 0

omit [Fintype Y] in
private theorem diffAct_apply_of_eq_zero {n : ℕ} (hn : n = 0) (b : Fin n → B) (φ : Y → A) :
    diffAct dA n b φ = fun y => dA (φ y) := by
  subst hn
  rfl

omit [Fintype Y] in
private theorem diffAct_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    diffAct (Y := Y) (B := B) dA n = 0 := by
  cases n with
  | zero => exact absurd rfl hn
  | succ n => rfl

/-- The first factor of the composite term with all the inputs is `δ_{n+1}(b)`. -/
private theorem coeff_init (M : TypeDABimodule dA dB ιA ιB Y) {n : ℕ} (b : Fin n → B)
    (k : Fin (n + 1)) (hk : (k : ℕ) = n) :
    (M.coeff k fun l => b ⟨l, by have := l.isLt; have := k.isLt; omega⟩) = M.coeff n b := by
  obtain ⟨k, hk'⟩ := k
  simp only at hk
  subst hk
  rfl

/-- The second factor of the composite term with all the inputs is `δ_{n+1}(b)`. -/
private theorem coeff_tail (M : TypeDABimodule dA dB ιA ιB Y) {n : ℕ} (b : Fin n → B)
    (k : Fin (n + 1)) (hk : (k : ℕ) = 0) :
    (M.coeff (n - k) fun l => b ⟨k + l, by have := l.isLt; omega⟩) = M.coeff n b := by
  obtain ⟨k, hk'⟩ := k
  simp only at hk
  subst hk
  congr
  funext l
  exact congrArg b (Fin.ext (by simp))

/-- The operations of the induced module: `m_{n+1}(φ, b) = φ ⬝ δ_{n+1}(b)`, plus `d φ` for
`n = 0`. -/
private noncomputable def inducedAct (M : TypeDABimodule dA dB ιA ιB Y) (n : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin n => B) ((Y → A) →ₗ[R] Y → A) :=
  (continuationMapLinear R A).compMultilinearMap (M.coeff n) + diffAct dA n

private theorem inducedAct_apply (M : TypeDABimodule dA dB ιA ιB Y) (n : ℕ) (b : Fin n → B)
    (φ : Y → A) :
    M.inducedAct n b φ = continuationMapLinear R A (M.coeff n b) φ + diffAct dA n b φ :=
  (rfl)

/-- The composite terms of the induced module: the composite terms of the structure relation and
the derivative of `δ_{n+1}`, the two copies of `d φ ⬝ δ_{n+1}` cancelling. -/
private theorem ungradedStasheffComp_inducedAct [CharP R 2] (hdA : IsUngradedDGAlgebra dA)
    (M : TypeDABimodule dA dB ιA ιB Y) (n : ℕ) (b : Fin n → B) (φ : Y → A) :
    ungradedStasheffComp M.inducedAct n b φ =
      continuationMapLinear R A (typeDAStasheffComp M.coeff n b) φ +
        continuationMapLinear R A ((M.coeff n b).map dA) φ := by
  simp only [ungradedStasheffComp_def, inducedAct_apply, map_add, Finset.sum_add_distrib]
  -- The four kinds of terms: `φ ⬝ δ ⬝ δ`, `d φ ⬝ δ` from the left end, `d (φ ⬝ δ)` from the right
  -- end, and `d d φ`.
  have h1 : ∑ k : Fin (n + 1),
      continuationMapLinear R A (M.coeff (n - k) fun l => b ⟨k + l, by have := l.isLt; omega⟩)
        (continuationMapLinear R A
          (M.coeff k fun l => b ⟨l, by have := l.isLt; have := k.isLt; omega⟩) φ) =
      continuationMapLinear R A (typeDAStasheffComp M.coeff n b) φ := by
    rw [typeDAStasheffComp_def, map_sum, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun k _ => by
      simp only [continuationMapLinear_apply, continuationMap_matMul, LinearMap.comp_apply]
  have h2 : ∑ k : Fin (n + 1),
      continuationMapLinear R A (M.coeff (n - k) fun l => b ⟨k + l, by have := l.isLt; omega⟩)
        (diffAct dA k (fun l => b ⟨l, by have := l.isLt; have := k.isLt; omega⟩) φ) =
      continuationMapLinear R A (M.coeff n b) fun y => dA (φ y) := by
    rw [Finset.sum_eq_single 0 (fun k _ hk => by
      rw [diffAct_of_ne_zero (Fin.val_ne_iff.mpr hk), zero_apply, LinearMap.zero_apply,
        map_zero]) (by simp), diffAct_apply_of_eq_zero (by simp)]
    rw [M.coeff_tail b 0 (by simp)]
  have h3 : ∑ k : Fin (n + 1),
      diffAct dA (n - k) (fun l => b ⟨k + l, by have := l.isLt; omega⟩)
        (continuationMapLinear R A
          (M.coeff k fun l => b ⟨l, by have := l.isLt; have := k.isLt; omega⟩) φ) =
      continuationMapLinear R A (M.coeff n b) (fun y => dA (φ y)) +
        continuationMapLinear R A ((M.coeff n b).map dA) φ := by
    rw [Finset.sum_eq_single (Fin.last n) (fun k _ hk => by
      rw [diffAct_of_ne_zero (by
          have h := Fin.val_ne_iff.mpr hk
          rw [Fin.val_last] at h
          have := k.isLt
          omega), zero_apply, LinearMap.zero_apply]) (by simp),
      diffAct_apply_of_eq_zero (by simp), M.coeff_init b (Fin.last n) (by simp)]
    simp only [continuationMapLinear_apply]
    exact funext fun y => hdA.isUngradedDGRightModule.map_continuationMap φ (M.coeff n b) y
  have h4 : ∑ k : Fin (n + 1),
      diffAct dA (n - k) (fun l => b ⟨k + l, by have := l.isLt; omega⟩)
        (diffAct dA k (fun l => b ⟨l, by have := l.isLt; have := k.isLt; omega⟩) φ) = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : (k : ℕ) = 0
    · by_cases hnk : n - k = 0
      · rw [diffAct_apply_of_eq_zero hk, diffAct_apply_of_eq_zero hnk]
        funext y
        exact hdA.map_map (φ y)
      · rw [diffAct_of_ne_zero hnk, zero_apply, LinearMap.zero_apply]
    · rw [diffAct_of_ne_zero hk, zero_apply, LinearMap.zero_apply, map_zero]
  rw [h1, h2, h3, h4, add_zero]
  have key (C X D : Y → A) : C + (X + D) + X = C + D := by
    rw [add_comm X D, add_assoc, add_assoc, add_self_eq_zero_of_charTwo R, add_zero]
  exact key _ _ _

/-- The differential terms of the induced module are those of the structure relation. -/
private theorem ungradedStasheffDiff_inducedAct (M : TypeDABimodule dA dB ιA ιB Y) (n : ℕ)
    (b : Fin n → B) (φ : Y → A) :
    ungradedStasheffDiff M.inducedAct dB n b φ =
      continuationMapLinear R A (typeDAStasheffDiff M.coeff dB n b) φ := by
  rw [ungradedStasheffDiff_def, typeDAStasheffDiff_def, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [inducedAct_apply, diffAct_of_ne_zero (by have := l.isLt; omega), zero_apply,
    LinearMap.zero_apply, add_zero]

/-- The product terms of the induced module are those of the structure relation. -/
private theorem ungradedStasheffMul_inducedAct (M : TypeDABimodule dA dB ιA ιB Y) (n : ℕ)
    (b : Fin n → B) (φ : Y → A) :
    ungradedStasheffMul M.inducedAct n b φ =
      continuationMapLinear R A (typeDAStasheffMul M.coeff n b) φ := by
  cases n with
  | zero => simp
  | succ n =>
    rw [ungradedStasheffMul_succ, typeDAStasheffMul_succ, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [inducedAct_apply, diffAct_of_ne_zero (by have := l.isLt; omega), zero_apply,
      LinearMap.zero_apply, add_zero]

variable [CharP R 2]

/-- The **induced module** `A ⊠ M` of a type `DA` bimodule, over a ring of characteristic two:
the row vectors `φ : Y → A` with the operations `m₁(φ) = d φ + φ ⬝ δ₁` and
`m_{n+1}(φ, b₁, …, bₙ) = φ ⬝ δ_{n+1}(b₁, …, bₙ)` form an ungraded `A∞` right module over `B`. Its
`A∞` relation of length `n` is the structure relation of length `n` acting on `φ`. -/
noncomputable def inducedModule (hdA : IsUngradedDGAlgebra dA) (M : TypeDABimodule dA dB ιA ιB Y) :
    UngradedAInfinityRightModule dB (Y → A) where
  act := M.inducedAct
  stasheff n b φ := by
    rw [ungradedStasheffComp_inducedAct hdA, ungradedStasheffDiff_inducedAct,
      ungradedStasheffMul_inducedAct, add_comm (continuationMapLinear R A _ φ),
      ← LinearMap.add_apply, ← map_add, ← LinearMap.add_apply, ← map_add, ← LinearMap.add_apply,
      ← map_add, M.stasheff n b, map_zero, LinearMap.zero_apply]

private theorem inducedModule_act (hdA : IsUngradedDGAlgebra dA)
    (M : TypeDABimodule dA dB ιA ιB Y) : (M.inducedModule hdA).act = M.inducedAct :=
  (rfl)

/-- The operation `m₁` of the induced module is `φ ↦ d φ + φ ⬝ δ₁`. -/
@[simp]
theorem inducedModule_act_zero (hdA : IsUngradedDGAlgebra dA) (M : TypeDABimodule dA dB ιA ιB Y)
    (b : Fin 0 → B) (φ : Y → A) :
    (M.inducedModule hdA).act 0 b φ =
      (fun y => dA (φ y)) + continuationMap R A (M.coeff 0 b) φ := by
  rw [inducedModule_act, inducedAct_apply, diffAct_apply_of_eq_zero rfl,
    continuationMapLinear_apply, add_comm]

/-- The higher operations of the induced module are `φ ↦ φ ⬝ δ_{n+2}(b)`. -/
@[simp]
theorem inducedModule_act_succ (hdA : IsUngradedDGAlgebra dA) (M : TypeDABimodule dA dB ιA ιB Y)
    (n : ℕ) (b : Fin (n + 1) → B) (φ : Y → A) :
    (M.inducedModule hdA).act (n + 1) b φ = continuationMap R A (M.coeff (n + 1) b) φ := by
  rw [inducedModule_act, inducedAct_apply, diffAct_of_ne_zero n.succ_ne_zero, zero_apply,
    LinearMap.zero_apply, add_zero, continuationMapLinear_apply]

/-- The `y'`-component of an operation of the induced module. -/
theorem inducedModule_act_apply (hdA : IsUngradedDGAlgebra dA)
    (M : TypeDABimodule dA dB ιA ιB Y) (n : ℕ) (b : Fin n → B) (φ : Y → A) (y' : Y) :
    (M.inducedModule hdA).act n b φ y' =
      ∑ y, φ y * M.coeff n b y y' + if n = 0 then dA (φ y') else 0 := by
  cases n with
  | zero =>
    rw [inducedModule_act_zero, Pi.add_apply, add_comm]
    simp only [↓reduceIte, continuationMap_apply (R := R) (M := A) (M.coeff 0 b), op_smul_eq_mul]
  | succ n =>
    rw [inducedModule_act_succ]
    simp only [Nat.succ_ne_zero, ↓reduceIte, add_zero,
      continuationMap_apply (R := R) (M := A) (M.coeff (n + 1) b), op_smul_eq_mul]

end Induced

/-! ### The box tensor product with a type `D` structure -/

section BoxTensor

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The sum over the paths `x = x₀ → ⋯ → xₙ = z` in `X` of `δ_{n+1}(ε x₀ x₁, …, ε xₙ₋₁ xₙ)`, for
the coefficient matrix `ε` of a type `D` structure: the part of the box tensor coefficients coming
from `δ¹_{n+1}`. -/
noncomputable def pathCoeff (M : TypeDABimodule dA dB ιA ιB Y) (N : TypeDStructure dB ιB X)
    (n : ℕ) (x z : X) : Matrix Y Y A :=
  PiTensorProduct.lift (M.coeff n) (N.iteratedCoeff n x z)

/-- **The path coefficients in terms of the iterates of `N`**: `δ_{n+1}` evaluated on the iterate
`δⁿ`, the coefficient of `z` in `δⁿ(x)`. -/
theorem pathCoeff_def (M : TypeDABimodule dA dB ιA ιB Y) (N : TypeDStructure dB ιB X) (n : ℕ)
    (x z : X) : M.pathCoeff N n x z = PiTensorProduct.lift (M.coeff n) (N.iteratedCoeff n x z) :=
  (rfl)

/-- The entries of the path coefficients. -/
theorem pathCoeff_apply (M : TypeDABimodule dA dB ιA ιB Y) (N : TypeDStructure dB ιB X)
    (n : ℕ) (x z : X) (y y' : Y) :
    M.pathCoeff N n x z y y' = ∑ r : Fin (n + 1) → X,
      if r 0 = x ∧ r (Fin.last n) = z then
        M.coeff n (fun l => N.coeff (r l.castSucc) (r l.succ)) y y'
      else 0 := by
  rw [pathCoeff_def, N.lift_iteratedCoeff, Matrix.sum_apply, Finset.sum_filter]

/-- The **coefficients of the box tensor product** `M ⊠ N`: the coefficient of `y' ⊗ z` in
`δ¹(y ⊗ x)` is the sum over the paths `x = x₀ → ⋯ → xₙ = z` of the `(y, y')` entry of
`δ_{n+1}(ε x₀ x₁, …, ε xₙ₋₁ xₙ)`. The sum over `n` is finite when `N` is bounded or when `δ_{n+1}`
vanishes for large `n`. When the sequence of these entries has infinite support, this `finsum` is
`0` by convention. -/
noncomputable def boxCoeff (M : TypeDABimodule dA dB ιA ιB Y) (N : TypeDStructure dB ιB X) :
    Matrix (Y × X) (Y × X) A :=
  fun p q => ∑ᶠ n, M.pathCoeff N n p.2 q.2 p.1 q.1

/-- The box tensor coefficients as the `finsum` of the path coefficients. -/
theorem boxCoeff_apply (M : TypeDABimodule dA dB ιA ιB Y) (N : TypeDStructure dB ιB X)
    (p q : Y × X) : M.boxCoeff N p q = ∑ᶠ n, M.pathCoeff N n p.2 q.2 p.1 q.1 :=
  (rfl)

/-- An additive map fixing every path coefficient entry fixes the box tensor coefficient. -/
private theorem map_boxCoeff_eq_of_map_pathCoeff_eq (M : TypeDABimodule dA dB ιA ιB Y)
    (N : TypeDStructure dB ιB X) (f : A →+ A) (p q : Y × X)
    (h : ∀ n, f (M.pathCoeff N n p.2 q.2 p.1 q.1) = M.pathCoeff N n p.2 q.2 p.1 q.1) :
    f (M.boxCoeff N p q) = M.boxCoeff N p q := by
  rw [boxCoeff_apply]
  by_cases hfin : Function.HasFiniteSupport fun n => M.pathCoeff N n p.2 q.2 p.1 q.1
  · rw [map_finsum f hfin]
    exact finsum_congr h
  · rw [finsum_of_not_hasFiniteSupport hfin, map_zero]

/-- The box tensor coefficients lie in the summands of the left idempotents on the left. -/
theorem idem_mul_boxCoeff (M : TypeDABimodule dA dB ιA ιB Y) (N : TypeDStructure dB ιB X)
    (p q : Y × X) : ιA (M.idemLeft p.1) * M.boxCoeff N p q = M.boxCoeff N p q := by
  refine M.map_boxCoeff_eq_of_map_pathCoeff_eq N (AddMonoidHom.mulLeft _) p q fun n => ?_
  simp only [AddMonoidHom.coe_mulLeft, pathCoeff_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs
  · exact M.idem_mul_coeff _ _ _ _
  · simp

/-- The box tensor coefficients lie in the summands of the left idempotents on the right. -/
theorem boxCoeff_mul_idem (M : TypeDABimodule dA dB ιA ιB Y) (N : TypeDStructure dB ιB X)
    (p q : Y × X) : M.boxCoeff N p q * ιA (M.idemLeft q.1) = M.boxCoeff N p q := by
  refine M.map_boxCoeff_eq_of_map_pathCoeff_eq N (AddMonoidHom.mulRight _) p q fun n => ?_
  simp only [AddMonoidHom.coe_mulRight, pathCoeff_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs
  · exact M.coeff_mul_idem _ _ _ _
  · simp

/-- **No coefficient leaves the matched pairs.** If the idempotents of `B` are orthogonal, the
coefficient from a pair `y ⊗ x` with `idemRight y = idem x` to a pair `y' ⊗ z` with
`idemRight y' ≠ idem z` vanishes. -/
theorem boxCoeff_eq_zero_of_ne (hιB : ∀ t t', t ≠ t' → ιB t * ιB t' = 0)
    (M : TypeDABimodule dA dB ιA ιB Y) (N : TypeDStructure dB ιB X) {p q : Y × X}
    (hp : M.idemRight p.1 = N.idem p.2) (hq : M.idemRight q.1 ≠ N.idem q.2) :
    M.boxCoeff N p q = 0 := by
  rw [boxCoeff_apply]
  refine (finsum_congr fun n => ?_).trans finsum_zero
  rw [pathCoeff_apply]
  refine Finset.sum_eq_zero fun r _ => ?_
  split_ifs with hr
  · obtain ⟨hr0, hrz⟩ := hr
    cases n with
    | zero =>
      have hpq : p.2 = q.2 := by rw [← hr0, ← hrz]; rfl
      exact M.coeff_zero_eq_zero_of_ne _ (by rw [hp, hpq]; exact Ne.symm hq)
    | succ n =>
      rw [← M.coeff_succ_update_mul_idem]
      refine congrFun (congrFun ((M.coeff (n + 1)).map_coord_zero (Fin.last n) ?_) _) _
      rw [Function.update_self, Fin.succ_last, hrz, ← N.coeff_mul_idem, mul_assoc,
        hιB _ _ (Ne.symm hq), mul_zero]
  · rfl

/-- Some `K` bounds the lengths of the paths with nonzero path coefficients, when `N` is bounded
or `δ_{n+1}` vanishes for large `n`. -/
private theorem exists_forall_pathCoeff_eq_zero (M : TypeDABimodule dA dB ιA ιB Y)
    (N : TypeDStructure dB ιB X) (hMN : N.IsBounded ∨ ∃ K, ∀ n, K ≤ n → M.coeff n = 0) :
    ∃ K, ∀ n, K ≤ n → ∀ x z, M.pathCoeff N n x z = 0 := by
  rcases hMN with hN | ⟨K, hK⟩
  · obtain ⟨K, hK⟩ := N.isBounded_iff.mp hN
    exact ⟨K, fun n hn x z => by rw [pathCoeff_def, hK n hn, map_zero]⟩
  · refine ⟨K, fun n hn x z => ?_⟩
    simp [pathCoeff_def, hK n hn]

/-- **The box tensor coefficients as a finite sum.** If the path coefficients vanish for paths of
length at least `K`, the box tensor coefficients are the sums of the path coefficients of length
less than `K`. -/
theorem boxCoeff_eq_sum (M : TypeDABimodule dA dB ιA ιB Y) (N : TypeDStructure dB ιB X) {K : ℕ}
    (hK : ∀ n, K ≤ n → ∀ x z, M.pathCoeff N n x z = 0) (p q : Y × X) :
    M.boxCoeff N p q = ∑ n ∈ range K, M.pathCoeff N n p.2 q.2 p.1 q.1 := by
  refine finsum_eq_sum_of_support_subset _ fun n hn => ?_
  rw [Function.mem_support] at hn
  simp only [coe_range, Set.mem_Iio]
  by_contra h
  exact hn (by rw [hK n (not_lt.mp h)]; rfl)

/-- **The box tensor coefficients of a bounded bimodule.** If `δ_{n+1}` vanishes for `n ≥ K`, the
coefficient of `y' ⊗ z` in `δ¹(y ⊗ x)` is the sum over the paths `x = x₀ → ⋯ → xₙ = z` of length
`n < K` of the `(y, y')` entry of `δ_{n+1}(ε x₀ x₁, …, ε xₙ₋₁ xₙ)`. -/
theorem boxCoeff_eq_sum_of_coeff_eq_zero (M : TypeDABimodule dA dB ιA ιB Y)
    (N : TypeDStructure dB ιB X) {K : ℕ} (hK : ∀ n, K ≤ n → M.coeff n = 0) (p q : Y × X) :
    M.boxCoeff N p q = ∑ n ∈ range K, M.pathCoeff N n p.2 q.2 p.1 q.1 :=
  M.boxCoeff_eq_sum N (fun n hn x z => by simp [pathCoeff_def, hK n hn]) p q

/-- **The box tensor coefficients with a bounded type `D` structure.** If the iterates `δⁿ` of `N`
vanish for `n ≥ K`, the coefficient of `y' ⊗ z` in `δ¹(y ⊗ x)` is the `(y, y')` entry of
`∑_{n < K} δ_{n+1}(δⁿ(x))`, the iterate taken at `z`. -/
theorem boxCoeff_eq_sum_lift_iteratedCoeff (M : TypeDABimodule dA dB ιA ιB Y)
    (N : TypeDStructure dB ιB X) {K : ℕ} (hK : ∀ n, K ≤ n → ∀ x z, N.iteratedCoeff n x z = 0)
    (p q : Y × X) :
    M.boxCoeff N p q =
      ∑ n ∈ range K, PiTensorProduct.lift (M.coeff n) (N.iteratedCoeff n p.2 q.2) p.1 q.1 := by
  rw [M.boxCoeff_eq_sum N (K := K) (fun n hn x z => by rw [pathCoeff_def, hK n hn, map_zero])]
  simp only [pathCoeff_def]

/-- **The box tensor product with a differential bimodule.** If `δ_{n+1}` vanishes for `n ≥ 2`,
the coefficient of `y' ⊗ z` in `δ¹(y ⊗ x)` is the `(y, y')` entry of `δ₁` if `x = z`, plus that of
`δ₂(ε x z)`: `δ¹(y ⊗ x) = δ¹₁(y) ⊗ x + ∑_z δ¹₂(y, ε x z) ⊗ z`. -/
theorem boxCoeff_eq_add_of_coeff_eq_zero (M : TypeDABimodule dA dB ιA ιB Y)
    (N : TypeDStructure dB ιB X) (hM : ∀ n, 2 ≤ n → M.coeff n = 0) (y y' : Y) (x z : X) :
    M.boxCoeff N (y, x) (y', z) =
      (if x = z then M.coeff 0 ![] y y' else 0) + M.coeff 1 ![N.coeff x z] y y' := by
  rw [M.boxCoeff_eq_sum_of_coeff_eq_zero N hM, Finset.sum_range_succ, Finset.sum_range_one,
    pathCoeff_def, pathCoeff_def, N.iteratedCoeff_zero,
    N.iteratedCoeff_one, PiTensorProduct.lift.tprod]
  congr 1
  · split_ifs
    · rw [PiTensorProduct.lift.tprod, Subsingleton.elim Fin.elim0 ![]]
    · rw [map_zero, Matrix.zero_apply]
  · rw [show (fun _ : Fin 1 => N.coeff x z) = ![N.coeff x z] from
      funext fun l => by rw [Fin.fin_one_eq_zero l]; rfl]

variable [CharP R 2]

/-- The operations of the matrix module of the induced module along the coefficient matrix of
`N` are given by the path coefficients, together with `d Φ` for `n = 0`. -/
theorem matrixAct_inducedModule_apply (hdA : IsUngradedDGAlgebra dA)
    (M : TypeDABimodule dA dB ιA ιB Y) (N : TypeDStructure dB ιB X) (n : ℕ) (Φ : X → Y → A)
    (z : X) (y' : Y) :
    (M.inducedModule hdA).matrixAct X n (fun _ => N.coeff) Φ z y' =
      ∑ x, ∑ y, Φ x y * M.pathCoeff N n x z y y' + if n = 0 then dA (Φ z y') else 0 := by
  rw [UngradedAInfinityRightModule.matrixAct_apply, Finset.sum_apply]
  simp only [apply_ite (fun f : Y → A => f y'), Pi.zero_apply, inducedModule_act_apply]
  have ha : ∑ x, ∑ y, Φ x y * M.pathCoeff N n x z y y' =
      ∑ r : Fin (n + 1) → X with r (Fin.last n) = z,
        ∑ y, Φ (r 0) y * M.coeff n (fun l => N.coeff (r l.castSucc) (r l.succ)) y y' := by
    refine (Finset.sum_congr rfl fun x _ => ?_).trans (N.sum_lift_iteratedCoeff n
      (fun x => (∑ y, LinearMap.mulLeft R (Φ x y) ∘ₗ
        Matrix.entryLinearMap R A y y').compMultilinearMap (M.coeff n)) z |>.trans ?_)
    · simp only [pathCoeff_def, N.lift_iteratedCoeff, Matrix.sum_apply, Finset.mul_sum,
        LinearMap.compMultilinearMap_apply, LinearMap.sum_apply, LinearMap.comp_apply,
        Matrix.entryLinearMap_apply, LinearMap.mulLeft_apply]
      exact Finset.sum_comm
    · simp
  have hb : ∑ r : Fin (n + 1) → X,
      (if r (Fin.last n) = z then (if n = 0 then dA (Φ (r 0) y') else 0) else 0) =
      if n = 0 then dA (Φ z y') else 0 := by
    by_cases hn : n = 0
    · subst hn
      rw [← (Equiv.funUnique (Fin 1) X).symm.sum_comp]
      simp
    · simp [hn]
  rw [ha, Finset.sum_filter, ← hb, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs <;> simp

/-- **The box tensor differential of the induced module.** When `N` is bounded or `δ_{n+1}`
vanishes for large `n`, the box tensor differential of the induced module `A ⊠ M` with `N`, on the
row vectors `Φ : X → Y → A`, is `Φ ↦ d Φ + Φ ⬝ C` for the box tensor coefficients `C`. -/
theorem typeABoxDifferential_inducedModule_apply (hdA : IsUngradedDGAlgebra dA)
    (M : TypeDABimodule dA dB ιA ιB Y) (N : TypeDStructure dB ιB X)
    (hMN : N.IsBounded ∨ ∃ K, ∀ n, K ≤ n → M.coeff n = 0) (Φ : X → Y → A) (z : X) (y' : Y) :
    N.typeABoxDifferential (M.inducedModule hdA) Φ z y' =
      dA (Φ z y') + ∑ x, ∑ y, Φ x y * M.boxCoeff N (y, x) (y', z) := by
  obtain ⟨K, hK⟩ := M.exists_forall_pathCoeff_eq_zero N hMN
  have hK' : ∀ n, K + 1 ≤ n →
      ((M.inducedModule hdA).matrixAct X n fun _ => N.coeff) = 0 := fun n hn =>
    LinearMap.ext fun Φ => funext fun z => funext fun y' => by
      have hn0 : n ≠ 0 := by omega
      simp [matrixAct_inducedModule_apply, hn0, hK n (by omega)]
  rw [TypeDStructure.typeABoxDifferential_def,
    UngradedAInfinityRightModule.twistedDifferential_eq_sum _
    (by simpa only [UngradedAInfinityRightModule.matrix_act] using hK')]
  simp only [LinearMap.sum_apply, Finset.sum_apply, UngradedAInfinityRightModule.matrix_act,
    matrixAct_inducedModule_apply, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_range,
    Nat.zero_lt_succ, ↓reduceIte]
  rw [add_comm]
  congr 1
  simp only [M.boxCoeff_eq_sum N (K := K + 1) (fun n hn => hK n (by omega)), Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_comm

/-- **The structure equation of the box tensor product** on all pairs of generators. If `N` is
bounded or `δ_{n+1}` vanishes for large `n`, the box tensor coefficients satisfy
`d C + C C = 0`, over a ring of characteristic two. -/
theorem map_boxCoeff_add_boxCoeff_mul_boxCoeff (hdA : IsUngradedDGAlgebra dA)
    (M : TypeDABimodule dA dB ιA ιB Y) (N : TypeDStructure dB ιB X)
    (hMN : N.IsBounded ∨ ∃ K, ∀ n, K ≤ n → M.coeff n = 0) :
    (M.boxCoeff N).map dA + M.boxCoeff N * M.boxCoeff N = 0 := by
  classical
  have hDD (Φ : X → Y → A) : N.typeABoxDifferential (M.inducedModule hdA)
      (N.typeABoxDifferential (M.inducedModule hdA) Φ) = 0 := by
    rcases hMN with hN | ⟨K, hK⟩
    · exact N.typeABoxDifferential_typeABoxDifferential_of_isBounded _ hN Φ
    · refine N.typeABoxDifferential_typeABoxDifferential_of_act_eq_zero _ (K := K + 1)
        (fun n hn => ?_) Φ
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      refine MultilinearMap.ext fun b => LinearMap.ext fun φ => ?_
      rw [inducedModule_act_succ, hK (m + 1) (by omega)]
      simp
  ext p q
  obtain ⟨y, x⟩ := p
  obtain ⟨y'', z'⟩ := q
  -- The box tensor differential of the elementary row vector `y ⊗ x` is the row of `C` at `y ⊗ x`.
  have hΦ (z : X) (y' : Y) : N.typeABoxDifferential (M.inducedModule hdA)
      (Pi.single x (Pi.single y 1)) z y' = M.boxCoeff N (y, x) (y', z) := by
    rw [typeABoxDifferential_inducedModule_apply hdA M N hMN]
    simp [Pi.single_apply, ite_apply, apply_ite dA, hdA.map_one, ite_mul]
  have h := congrFun (congrFun (hDD (Pi.single x (Pi.single y 1))) z') y''
  rw [typeABoxDifferential_inducedModule_apply hdA M N hMN] at h
  simp only [hΦ] at h
  rw [Matrix.add_apply, Matrix.map_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    Finset.sum_comm]
  simpa using h

/-- The **box tensor product** `M ⊠ N` of a type `DA` bimodule with a type `D` structure, over a
ring of characteristic two: the type `D` structure over `A` on the pairs `y ⊗ x` of generators with
matching idempotents `idemRight y = idem x`, with the box tensor coefficients
`TauCeti.TypeDABimodule.boxCoeff`. The idempotents of `B` are orthogonal, and either `N` is
bounded or `δ_{n+1}` vanishes for large `n`. -/
noncomputable def boxTensor [DecidableEq T] (hdA : IsUngradedDGAlgebra dA)
    (hιB : ∀ t t', t ≠ t' → ιB t * ιB t' = 0) (M : TypeDABimodule dA dB ιA ιB Y)
    (N : TypeDStructure dB ιB X) (hMN : N.IsBounded ∨ ∃ K, ∀ n, K ≤ n → M.coeff n = 0) :
    TypeDStructure dA ιA {p : Y × X // M.idemRight p.1 = N.idem p.2} where
  idem p := M.idemLeft p.1.1
  coeff p q := M.boxCoeff N p.1 q.1
  idem_mul_coeff p q := M.idem_mul_boxCoeff N p.1 q.1
  coeff_mul_idem p q := M.boxCoeff_mul_idem N p.1 q.1
  map_coeff_add_coeff_mul_coeff := by
    ext p q
    have h := congrFun (congrFun (M.map_boxCoeff_add_boxCoeff_mul_boxCoeff hdA N hMN) p.1) q.1
    have h0 : ∑ r : {r : Y × X // ¬M.idemRight r.1 = N.idem r.2},
        M.boxCoeff N p.1 r.1 * M.boxCoeff N r.1 q.1 = 0 :=
      Finset.sum_eq_zero fun r _ => by rw [M.boxCoeff_eq_zero_of_ne hιB N p.2 r.2, zero_mul]
    rw [Matrix.add_apply, Matrix.mul_apply, ← Fintype.sum_subtype_add_sum_subtype
      (fun r : Y × X => M.idemRight r.1 = N.idem r.2), h0, add_zero] at h
    rw [Matrix.map_apply, Matrix.zero_apply] at h
    -- The coefficients are the plain function `fun p q => M.boxCoeff N p.1 q.1` rather than a
    -- `Matrix`-typed term, so `Matrix.map_apply` and `Matrix.mul_apply` do not rewrite them; the
    -- remaining goal is `h` after unfolding `Matrix.map` and the matrix product.
    rw [Matrix.add_apply, Matrix.zero_apply]
    exact h

section BoxTensorStructure

variable [DecidableEq T] {hdA : IsUngradedDGAlgebra dA} {hιB : ∀ t t', t ≠ t' → ιB t * ιB t' = 0}
  {M : TypeDABimodule dA dB ιA ιB Y} {N : TypeDStructure dB ιB X}
  {hMN : N.IsBounded ∨ ∃ K, ∀ n, K ≤ n → M.coeff n = 0}

@[simp]
theorem boxTensor_idem (p : {p : Y × X // M.idemRight p.1 = N.idem p.2}) :
    (boxTensor hdA hιB M N hMN).idem p = M.idemLeft p.1.1 :=
  (rfl)

@[simp]
theorem boxTensor_coeff (p q : {p : Y × X // M.idemRight p.1 = N.idem p.2}) :
    (boxTensor hdA hιB M N hMN).coeff p q = M.boxCoeff N p.1 q.1 :=
  (rfl)

end BoxTensorStructure

end BoxTensor

end TypeDABimodule

end TauCeti
