/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Fin.Basic
public import TauCeti.Geometry.Neuromanifold.Chain
public import TauCeti.Geometry.Neuromanifold.Polynomial.Homogeneous
import TauCeti.Geometry.Neuromanifold.Polynomial.Map

/-!
# Finite chains of jointly polynomial models

Given a finite sequence of jointly polynomial layer models
`P : ∀ i : Fin n, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K`, with varying intermediate
coordinate types `I` and layer parameter-variable types `W`, iterated polynomial substitution
assembles a single jointly polynomial model `polynomialChain P` whose parameter variables are the
dependent sum `Σ i, W i` and whose input variables are `I 0`:

* `polynomialChainPrefix P k` gives the prefix tuple at intermediate stage `k : Fin (n + 1)`,
  starting from the input variables at `0` and substituting the preceding prefix into `P i` while
  tagging `W i` with layer index `i`; `polynomialChain P` is the final prefix at `Fin.last n`, and
  `polynomialChain_eq_dfoldl` identifies it with the dependent left fold `Fin.dfoldl`.
* Splitting off the first or the last layer (`polynomialChain_succ`, `polynomialChain_succ_last`)
  writes `polynomialChain P` in terms of binary `polynomialCompose` up to parameter-variable
  renaming.
* `polynomialRealization_polynomialChain` identifies `polynomialRealization (polynomialChain P)`
  with `chain (fun i => polynomialRealization (P i))` after currying parameter coordinates along
  `Equiv.piCurry`, so `realizedFunctions_polynomialChain` identifies their neuromanifolds.
* Layerwise polynomial reparametrization (`polynomialChain_polynomialReparametrize`) and scalar
  ring-homomorphism transport (`map_polynomialChain`) commute with chain composition.
* With finite coordinate types, the uniform input-degree bound of prefix `k` is at most
  `Fin.partialProd (fun i => polynomialInputDegree (P i)) k`
  (`polynomialInputDegree_polynomialChainPrefix_le`), so `polynomialChain P` has uniform
  input-degree bound at most `∏ i, polynomialInputDegree (P i)`
  (`polynomialInputDegree_polynomialChain_le`). When each layer `P i` is homogeneous in its inputs
  of degree `d i`, prefix `k` is homogeneous in the initial inputs of degree
  `Fin.partialProd d k` (`isHomogeneous_inputPolynomial_polynomialChainPrefix`), and
  `polynomialChain P` is homogeneous of degree `∏ i, d i`
  (`isHomogeneous_inputPolynomial_polynomialChain`).

Thus any finite chain built from the concrete polynomial layers of
`TauCeti.Geometry.Neuromanifold.Polynomial.Constructors` inherits the uniform input-degree bound,
faithful bounded-degree coefficient presentation, and scalar transport of the jointly polynomial
interface; chains of input-homogeneous layers (such as `polynomialLinear`,
`polynomialConvolution`, and monomial activations) also inherit the homogeneous coefficient
presentation via `isHomogeneous_inputPolynomial_polynomialChain`.

The layer-composition and jointly polynomial conventions follow
Marchetti–Shahverdi–Mereta–Trager–Kohn,
*Algebra Unveils Deep Learning — An Invitation to Neuroalgebraic Geometry*,
[arXiv:2501.18915v2](https://arxiv.org/abs/2501.18915v2), §3, equation (2) and §3.1. The
multiplicative homogeneity degree of composed homogeneous layers follows Finkel–Rodriguez–Wu–Yahl,
*Activation degree thresholds and expressiveness of polynomial neural networks*,
[arXiv:2408.04569v4](https://arxiv.org/abs/2408.04569v4), §1.1.
-/

public section

noncomputable section

namespace TauCeti.Neuromanifold

open MvPolynomial

variable {K : Type*} [CommSemiring K]
variable {n : ℕ} {I : Fin (n + 1) → Type*} {W : Fin n → Type*}

/-! ### Prefix and chain polynomial substitution -/

/-- The prefix polynomials of a finite chain of jointly polynomial layer models `P`, in the
dependent sum `Σ i, W i` of all layer parameter variables and the initial input variables `I 0`:
prefix `0` is the tuple of input variables, and prefix `i + 1` substitutes prefix `i` for the
inputs of `P i` while tagging the parameter variables of `P i` with layer index `i`. -/
def polynomialChainPrefix (P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K) :
    ∀ k, I k → MvPolynomial ((Σ i, W i) ⊕ I 0) K :=
  fun k =>
    Fin.dfoldl k.val (fun j => I (Fin.castLE k.isLt j) → MvPolynomial ((Σ i, W i) ⊕ I 0) K)
      (fun j prev o =>
        aeval (Sum.elim (fun w => X (Sum.inl ⟨Fin.castLE (Nat.le_of_lt_succ k.isLt) j, w⟩)) prev)
          (P (Fin.castLE (Nat.le_of_lt_succ k.isLt) j) o))
      (fun a => X (Sum.inr a))

/-- The zeroth prefix of a chain of polynomial models is the tuple of input variables. -/
@[simp] theorem polynomialChainPrefix_zero
    (P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K) :
    polynomialChainPrefix P 0 = fun a => X (Sum.inr a) :=
  Fin.dfoldl_castLE_zero
    (α := fun k => I k → MvPolynomial ((Σ i, W i) ⊕ I 0) K)
    (fun j prev o => aeval (Sum.elim (fun w => X (Sum.inl ⟨j, w⟩)) prev) (P j o))
    (fun a => X (Sum.inr a))

/-- Each step of `polynomialChainPrefix` substitutes the preceding prefix for the layer's inputs
and tags the layer's parameter variables with its index. -/
@[simp] theorem polynomialChainPrefix_succ
    (P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K) (i : Fin n) (o : I i.succ) :
    polynomialChainPrefix P i.succ o =
      aeval (Sum.elim (fun w => X (Sum.inl ⟨i, w⟩)) (polynomialChainPrefix P i.castSucc))
        (P i o) :=
  congrFun (Fin.dfoldl_castLE_succ
    (α := fun k => I k → MvPolynomial ((Σ i, W i) ⊕ I 0) K)
    (fun j prev o => aeval (Sum.elim (fun w => X (Sum.inl ⟨j, w⟩)) prev) (P j o))
    (fun a => X (Sum.inr a)) i) o

/-- Prefix `k` of `polynomialChainPrefix` depends only on the layers strictly below `k`. -/
theorem polynomialChainPrefix_congr
    {P Q : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K} {k : Fin (n + 1)}
    (h : ∀ i : Fin n, i.val < k.val → P i = Q i) :
    polynomialChainPrefix P k = polynomialChainPrefix Q k := by
  induction k using Fin.induction with
  | zero => simp
  | succ i ih =>
    funext o
    have hi : polynomialChainPrefix P i.castSucc = polynomialChainPrefix Q i.castSucc :=
      ih fun j hj => h j (Nat.lt_succ_of_lt hj)
    rw [polynomialChainPrefix_succ, polynomialChainPrefix_succ, hi, h i (Nat.lt_succ_self _)]

/-- Step `i + 1` of `polynomialChainPrefix` is the binary composition `polynomialCompose` of
prefix `i` with layer `P i`, after folding `W i` into `Σ j, W j`. -/
theorem polynomialChainPrefix_succ_eq_rename_polynomialCompose_last
    (P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K) (i : Fin n) :
    polynomialChainPrefix P i.succ = fun o =>
      rename (Sum.map (Sum.elim id (Sigma.mk i)) id)
        (polynomialCompose (polynomialChainPrefix P i.castSucc) (P i) o) := by
  funext o
  rw [polynomialChainPrefix_succ, polynomialCompose_apply, rename_aeval]
  refine congrArg (fun F => aeval F (P i o)) (funext fun x => ?_)
  rcases x with w | a
  · simp
  · simp only [Sum.elim_inr, ← AlgHom.comp_apply, rename_comp_rename, Sum.map_comp_map,
      Sum.elim_comp_inl, Function.id_comp, Sum.map_id_id, rename_id_apply]

/-- Every prefix `polynomialChainPrefix P k` is the `k.val`-step dependent left fold `Fin.dfoldl`
of layerwise polynomial substitution, starting from the input variables. -/
theorem polynomialChainPrefix_eq_dfoldl
    (P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K) (k : Fin (n + 1)) :
    polynomialChainPrefix P k =
      Fin.dfoldl k.val (fun j => I (Fin.castLE k.isLt j) → MvPolynomial ((Σ i, W i) ⊕ I 0) K)
        (fun j prev o =>
          aeval (Sum.elim (fun w => X (Sum.inl ⟨Fin.castLE (Nat.le_of_lt_succ k.isLt) j, w⟩)) prev)
            (P (Fin.castLE (Nat.le_of_lt_succ k.isLt) j) o))
        (fun a => X (Sum.inr a)) := (rfl)

/-- Compose a finite chain of jointly polynomial layer models `P` into a single jointly polynomial
model, with parameter variables `Σ i, W i` and input variables `I 0`. -/
def polynomialChain (P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K) :
    I (Fin.last n) → MvPolynomial ((Σ i, W i) ⊕ I 0) K :=
  polynomialChainPrefix P (Fin.last n)

/-- The composed chain polynomial tuple is the final prefix of `polynomialChainPrefix`. -/
theorem polynomialChain_def (P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K) :
    polynomialChain P = polynomialChainPrefix P (Fin.last n) := (rfl)

/-- The composed chain polynomial tuple is the dependent left fold `Fin.dfoldl` of layerwise
polynomial substitution, starting from the input variables. -/
theorem polynomialChain_eq_dfoldl
    (P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K) :
    polynomialChain P =
      Fin.dfoldl n (fun k => I k → MvPolynomial ((Σ i, W i) ⊕ I 0) K)
        (fun i prev o => aeval (Sum.elim (fun w => X (Sum.inl ⟨i, w⟩)) prev) (P i o))
        (fun a => X (Sum.inr a)) :=
  (polynomialChainPrefix_eq_dfoldl P (Fin.last n)).trans
    (Fin.dfoldl_castLE_last
      (α := fun k => I k → MvPolynomial ((Σ i, W i) ⊕ I 0) K)
      (fun i prev o => aeval (Sum.elim (fun w => X (Sum.inl ⟨i, w⟩)) prev) (P i o))
      (fun a => X (Sum.inr a)))

/-- The empty chain of polynomial models is the tuple of input variables. -/
@[simp] theorem polynomialChain_zero {I : Fin 1 → Type*} {W : Fin 0 → Type*}
    (P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K) :
    polynomialChain P = fun a => X (Sum.inr a) :=
  polynomialChainPrefix_zero P

/-- Restricting a chain to its first `n` layers renames the parameter variables in every prefix up
to `Fin.last n` along the inclusion `i ↦ i.castSucc` of layer indices. -/
theorem polynomialChainPrefix_castSucc {I : Fin (n + 2) → Type*} {W : Fin (n + 1) → Type*}
    (P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K) (k : Fin (n + 1))
    (o : I k.castSucc) :
    polynomialChainPrefix P k.castSucc o =
      rename (Sum.map (fun p => ⟨p.1.castSucc, p.2⟩) id)
        (polynomialChainPrefix (I := fun i => I i.castSucc) (fun i => P i.castSucc) k o) := by
  induction k using Fin.induction with
  | zero =>
    refine (congrFun (polynomialChainPrefix_zero P) o).trans ?_
    rw [polynomialChainPrefix_zero, rename_X, Sum.map_inr, id_eq]
    -- Both sides are `X (Sum.inr o)`; `I (Fin.castSucc 0)` is definitionally `I 0`.
    rfl
  | succ i ih =>
    -- `i.succ.castSucc` is definitionally `i.castSucc.succ`; `rw [← Fin.succ_castSucc]` cannot
    -- abstract `I` on the LHS alone while `P i.castSucc` fixes `I i.castSucc.succ` on the RHS.
    change polynomialChainPrefix P i.castSucc.succ o = _
    rw [polynomialChainPrefix_succ, polynomialChainPrefix_succ, rename_aeval]
    refine congrArg (fun F => aeval F (P i.castSucc o)) (funext fun x => ?_)
    rcases x with w | a
    · simp only [Sum.elim_inl, rename_X, Sum.map_inl]
      -- `⟨i, w⟩` projections reduce and `I (Fin.castSucc 0)` is defeq to `I 0` in the codomain.
      rfl
    · simp only [Sum.elim_inr, ih a]
      -- `I (Fin.castSucc 0)` is definitionally `I 0` in the codomain of `rename`.
      rfl

/-- Every positive prefix of a nonempty chain is the binary composition `polynomialCompose` of the
first layer `P 0` with the corresponding prefix of the tail chain, after folding the first-layer
and tail parameter variables into `Σ i, W i`. -/
theorem polynomialChainPrefix_succ_eq_rename_polynomialCompose
    {I : Fin (n + 2) → Type*} {W : Fin (n + 1) → Type*}
    (P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K) (k : Fin (n + 1)) (o : I k.succ) :
    polynomialChainPrefix P k.succ o =
      rename (Sum.map (Sum.elim (Sigma.mk 0) (fun p => ⟨p.1.succ, p.2⟩)) id)
        (polynomialCompose (P 0)
          (polynomialChainPrefix (I := fun i => I i.succ) (fun i => P i.succ) k) o) := by
  induction k using Fin.induction with
  | zero =>
    rw [polynomialChainPrefix_succ, polynomialChainPrefix_zero, polynomialCompose_apply]
    simp only [aeval_X, Sum.elim_inr, rename_rename]
    rw [rename_eq_aeval]
    refine congrArg (fun F => aeval F (P 0 o)) (funext fun x => ?_)
    rcases x with w | a
    · simp
    · simp only [Fin.castSucc_zero, polynomialChainPrefix_zero, Function.comp_apply]
      -- `Sum.elim`/`Sum.map` reduce on `Sum.inr a` with `a : I (Fin.castSucc 0)` defeq to `I 0`.
      rfl
  | succ i ih =>
    rw [polynomialChainPrefix_succ, polynomialCompose_apply, polynomialChainPrefix_succ,
      comp_aeval_apply (φ := aeval _), rename_aeval]
    refine congrArg (fun F => aeval F (P i.succ o)) (funext fun x => ?_)
    rcases x with w | a
    · simp only [Sum.elim_inl, aeval_X, rename_X, Sum.map_inl, Sum.elim_inr]
      -- `⟨i, w⟩` projections reduce and `I (Fin.castSucc 0)` is defeq to `I 0` in the codomain.
      rfl
    · simp only [Sum.elim_inr, ← polynomialCompose_apply]
      exact ih a

/-- Split off the first layer of `polynomialChain` as a binary `polynomialCompose`, folding the
first-layer and tail parameter variables into `Σ i, W i`. -/
theorem polynomialChain_succ {I : Fin (n + 2) → Type*} {W : Fin (n + 1) → Type*}
    (P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K) :
    polynomialChain P = fun o =>
      rename (Sum.map (Sum.elim (Sigma.mk 0) (fun p => ⟨p.1.succ, p.2⟩)) id)
        (polynomialCompose (P 0)
          (polynomialChain (I := fun i => I i.succ) (fun i => P i.succ)) o) :=
  funext (polynomialChainPrefix_succ_eq_rename_polynomialCompose P (Fin.last n))

/-- A one-layer chain of polynomial models renames the single layer's parameter variables into
`Σ i : Fin 1, W i`. -/
theorem polynomialChain_one {I : Fin 2 → Type*} {W : Fin 1 → Type*}
    (P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K) :
    polynomialChain P = fun o => rename (Sum.map (Sigma.mk 0) id) (P 0 o) := by
  rw [polynomialChain_succ, polynomialChain_zero]
  funext o
  rw [polynomialCompose_apply, aeval_X, Sum.elim_inr, rename_rename]
  simp [Sum.map_comp_map]

/-- Split off the last layer of `polynomialChain` as a binary `polynomialCompose`, folding the
prefix and last-layer parameter variables into `Σ i, W i`. -/
theorem polynomialChain_succ_last {I : Fin (n + 2) → Type*} {W : Fin (n + 1) → Type*}
    (P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K) :
    polynomialChain P = fun o =>
      rename (Sum.map (Sum.elim (fun p => ⟨p.1.castSucc, p.2⟩) (Sigma.mk (Fin.last n))) id)
        (polynomialCompose
          (polynomialChain (I := fun i => I i.castSucc) (fun i => P i.castSucc))
          (P (Fin.last n)) o) := by
  -- `polynomialChain P` is `polynomialChainPrefix P (Fin.last (n + 1))`, and `Fin.last (n + 1)` is
  -- definitionally `(Fin.last n).succ`.
  refine (polynomialChainPrefix_succ_eq_rename_polynomialCompose_last P (Fin.last n)).trans ?_
  funext o
  rw [polynomialCompose_apply, polynomialCompose_apply, rename_aeval, rename_aeval]
  refine congrArg (fun F => aeval F (P (Fin.last n) o)) (funext fun x => ?_)
  rcases x with w | a
  · simp only [Sum.elim_inl, rename_X, Sum.map_inl, Sum.elim_inr]
    -- `I (Fin.castSucc 0)` (the input index of `polynomialChain ... P.castSucc`) is defeq to
    -- `I 0`.
    rfl
  · simp only [Sum.elim_inr, polynomialChain_def]
    rw [rename_rename, rename_rename]
    refine (congrArg _ (polynomialChainPrefix_castSucc P (Fin.last n) a)).trans ?_
    refine (rename_rename _ _ _).trans ?_
    refine congrArg (fun f => rename f _) (funext fun y => ?_)
    rcases y <;> simp

/-! ### Evaluation and neuromanifolds -/

/-- Step `i + 1` of `polynomialChainPrefix` evaluates layer `P i` on the output of step `i`, using
the layer's slice `v ↦ w ⟨i, v⟩` of parameter coordinates. -/
@[simp] theorem polynomialRealization_polynomialChainPrefix_succ
    (P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K) (i : Fin n) (w : (Σ j, W j) → K)
    (x : I 0 → K) :
    polynomialRealization (polynomialChainPrefix P i.succ) w x =
      polynomialRealization (P i) (fun v => w ⟨i, v⟩)
        (polynomialRealization (polynomialChainPrefix P i.castSucc) w x) := by
  rw [polynomialChainPrefix_succ_eq_rename_polynomialCompose_last,
    polynomialRealization_rename_sumMap, polynomialRealization_polynomialCompose]
  simp [Equiv.sumArrowEquivProdArrow, Function.comp_def]

/-- Evaluating `polynomialChainPrefix P k` agrees with the `k.val`-step dependent left fold of the
layer realization maps. -/
theorem polynomialRealization_polynomialChainPrefix_eq_dfoldl
    (P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K) (w : (Σ i, W i) → K)
    (x : I 0 → K) (k : Fin (n + 1)) :
    polynomialRealization (polynomialChainPrefix P k) w x =
      Fin.dfoldl k.val (fun j => I (Fin.castLE k.isLt j) → K)
        (fun j => polynomialRealization (P (Fin.castLE (Nat.le_of_lt_succ k.isLt) j))
          (fun v => w ⟨Fin.castLE (Nat.le_of_lt_succ k.isLt) j, v⟩))
        x :=
  Fin.eq_dfoldl_of_zero_of_succ
    (fun i => polynomialRealization (P i) (fun v => w ⟨i, v⟩))
    x (fun j => polynomialRealization (polynomialChainPrefix P j) w x)
    (by rw [polynomialChainPrefix_zero, polynomialRealization_X_inr]; simp only [Function.comp_def])
    (fun i => polynomialRealization_polynomialChainPrefix_succ P i w x) k

/-- Evaluating `polynomialChain P` realizes the finite chain of layer realizations
`chain (fun i => polynomialRealization (P i))` after currying the parameter coordinates with
`Equiv.piCurry`. -/
@[simp] theorem polynomialRealization_polynomialChain
    (P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K) :
    polynomialRealization (polynomialChain P) =
      chain (X := fun k => I k → K) (fun i => polynomialRealization (P i)) ∘
        Equiv.piCurry (fun _ _ => K) := by
  funext w x
  rw [polynomialChain_def, Function.comp_apply, chain_eq_dfoldl]
  exact (polynomialRealization_polynomialChainPrefix_eq_dfoldl P w x (Fin.last n)).trans
    (Fin.dfoldl_castLE_last (α := fun k => I k → K)
      (fun i => polynomialRealization (P i) (fun v => w ⟨i, v⟩)) x)

/-- Composing a finite chain of polynomial models by substitution realizes the same functions as
composing their realization maps with `chain`. -/
theorem realizedFunctions_polynomialChain
    (P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K) :
    realizedFunctions (polynomialRealization (polynomialChain P)) =
      realizedFunctions (chain (X := fun k => I k → K) fun i => polynomialRealization (P i)) := by
  rw [polynomialRealization_polynomialChain, realizedFunctions_def, realizedFunctions_def,
    (Equiv.piCurry fun _ _ => K).surjective.range_comp]

/-! ### Input polynomials, reparametrization, homogeneity, and scalar transport -/

/-- Collecting the inputs at step `i + 1` of `polynomialChainPrefix` substitutes the collected
input polynomials of step `i` into those of layer `P i`, tagging layer `i`'s parameter variables
with `Sigma.mk i`. -/
theorem inputPolynomial_polynomialChainPrefix_succ
    (P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K) (i : Fin n) (o : I i.succ) :
    inputPolynomial (polynomialChainPrefix P i.succ) o =
      eval₂ (C.comp (rename (Sigma.mk i) : MvPolynomial (W i) K →ₐ[K]
          MvPolynomial (Σ j, W j) K))
        (inputPolynomial (polynomialChainPrefix P i.castSucc))
        (inputPolynomial (P i) o) := by
  have hstep :
      polynomialChainPrefix P i.succ =
        fun k => aeval (Sum.elim (fun w => rename Sum.inl (X ⟨i, w⟩))
          (polynomialChainPrefix P i.castSucc)) (P i k) := by
    funext k
    simp [polynomialChainPrefix_succ]
  rw [hstep, inputPolynomial_aeval_sumElim, rename_eq_aeval (Sigma.mk i)]
  simp only [Function.comp_def]

/-- Reparametrizing each layer `i` by `R i` reparametrizes every prefix of `polynomialChainPrefix`
by the induced substitution on `Σ i, W i`. -/
@[simp] theorem polynomialChainPrefix_polynomialReparametrize
    {V : Fin n → Type*} (R : ∀ i, W i → MvPolynomial (V i) K)
    (P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K) (k : Fin (n + 1)) :
    polynomialReparametrize (fun p => rename (Sigma.mk p.1) (R p.1 p.2))
        (polynomialChainPrefix P k) =
      polynomialChainPrefix (fun i => polynomialReparametrize (R i) (P i)) k := by
  induction k using Fin.induction with
  | zero =>
    funext a
    simp [polynomialReparametrize_apply]
  | succ i ih =>
    funext o
    rw [polynomialReparametrize_apply, polynomialChainPrefix_succ, polynomialChainPrefix_succ,
      polynomialReparametrize_apply, comp_aeval_apply, comp_aeval_apply]
    refine congrArg (fun F => aeval F (P i o)) (funext fun x => ?_)
    rcases x with w | a
    · simp only [Sum.elim_inl, aeval_X, rename_rename, aeval_rename, Function.comp_def]
      rw [rename_eq_aeval]
      simp only [Function.comp_def]
    · simp only [Sum.elim_inr, aeval_X, ← polynomialReparametrize_apply]
      exact congrFun ih a

/-- Reparametrizing each layer `i` by `R i` reparametrizes `polynomialChain P` by the induced
substitution on `Σ i, W i`. -/
@[simp] theorem polynomialChain_polynomialReparametrize
    {V : Fin n → Type*} (R : ∀ i, W i → MvPolynomial (V i) K)
    (P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K) :
    polynomialReparametrize (fun p => rename (Sigma.mk p.1) (R p.1 p.2)) (polynomialChain P) =
      polynomialChain (fun i => polynomialReparametrize (R i) (P i)) :=
  polynomialChainPrefix_polynomialReparametrize R P (Fin.last n)

/-- With finite coordinate types, the uniform input-degree bound of prefix `k` of
`polynomialChainPrefix P` is at most the partial product of the layer input-degree bounds. -/
theorem polynomialInputDegree_polynomialChainPrefix_le [∀ k, Fintype (I k)]
    (P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K) (k : Fin (n + 1)) :
    polynomialInputDegree (polynomialChainPrefix P k) ≤
      Fin.partialProd (fun i => polynomialInputDegree (P i)) k := by
  induction k using Fin.induction with
  | zero =>
    rw [Fin.partialProd_zero]
    refine (polynomialInputDegree_le_iff _).2 fun a => ?_
    rw [polynomialChainPrefix_zero, inputPolynomial_X_inr]
    exact (isHomogeneous_X _ a).totalDegree_le
  | succ i ih =>
    rw [polynomialChainPrefix_succ_eq_rename_polynomialCompose_last, Fin.partialProd_succ]
    exact (polynomialInputDegree_rename_sumMap_le _ _).trans <|
      (polynomialInputDegree_polynomialCompose_le _ _).trans (Nat.mul_le_mul_right _ ih)

/-- With finite coordinate types, the uniform input-degree bound of `polynomialChain P` is at most
the product of the layer input-degree bounds. -/
theorem polynomialInputDegree_polynomialChain_le [∀ k, Fintype (I k)]
    (P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K) :
    polynomialInputDegree (polynomialChain P) ≤ ∏ i, polynomialInputDegree (P i) := by
  simpa only [polynomialChain_def, Fin.partialProd_last] using
    polynomialInputDegree_polynomialChainPrefix_le P (Fin.last n)

/-- If each layer `P i` strictly below `k` is homogeneous in its inputs of degree `d i`, then
prefix `k` of `polynomialChainPrefix P` is homogeneous in the initial inputs of degree
`Fin.partialProd d k`. -/
theorem isHomogeneous_inputPolynomial_polynomialChainPrefix
    {P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K} {d : Fin n → ℕ}
    (k : Fin (n + 1))
    (hP : ∀ i : Fin n, i.val < k.val → ∀ o, (inputPolynomial (P i) o).IsHomogeneous (d i))
    (o : I k) :
    (inputPolynomial (polynomialChainPrefix P k) o).IsHomogeneous (Fin.partialProd d k) := by
  induction k using Fin.induction with
  | zero =>
    rw [polynomialChainPrefix_zero, inputPolynomial_X_inr, Fin.partialProd_zero]
    exact isHomogeneous_X _ o
  | succ i ih =>
    rw [polynomialChainPrefix_succ_eq_rename_polynomialCompose_last, Fin.partialProd_succ]
    exact isHomogeneous_inputPolynomial_rename_sumMap _
      (isHomogeneous_inputPolynomial_polynomialCompose
        (ih fun j hj => hP j (Nat.lt_succ_of_lt hj)) (hP i (Nat.lt_succ_self _))) o

/-- If each layer `P i` is homogeneous in its inputs of degree `d i`, then `polynomialChain P` is
homogeneous in the initial inputs of degree `∏ i, d i`. -/
theorem isHomogeneous_inputPolynomial_polynomialChain
    {P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K} {d : Fin n → ℕ}
    (hP : ∀ i o, (inputPolynomial (P i) o).IsHomogeneous (d i)) (o : I (Fin.last n)) :
    (inputPolynomial (polynomialChain P) o).IsHomogeneous (∏ i, d i) := by
  simpa only [polynomialChain_def, Fin.partialProd_last] using
    isHomogeneous_inputPolynomial_polynomialChainPrefix (Fin.last n) (fun i _ => hP i) o

/-- Transporting `polynomialChainPrefix` along a ring homomorphism transports each layer model. -/
@[simp] theorem map_polynomialChainPrefix {L : Type*} [CommSemiring L] (φ : K →+* L)
    (P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K) (k : Fin (n + 1)) (o : I k) :
    map φ (polynomialChainPrefix P k o) =
      polynomialChainPrefix (fun i => map φ ∘ P i) k o := by
  induction k using Fin.induction with
  | zero => simp
  | succ i ih =>
    rw [polynomialChainPrefix_succ_eq_rename_polynomialCompose_last,
      polynomialChainPrefix_succ_eq_rename_polynomialCompose_last, map_rename,
      map_polynomialCompose]
    congr 2
    exact funext ih

/-- Transporting a prefix of coordinatewise `Polynomial.aeval` layers along a ring homomorphism
transports each layer model and maps the activation polynomials. -/
theorem map_polynomialChainPrefix_aeval {L : Type*} [CommSemiring L] (φ : K →+* L)
    {P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K}
    {Q : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) L}
    {p : ∀ i, I i.succ → Polynomial K} {q : ∀ i, I i.succ → Polynomial L}
    (hP : ∀ i o, map φ (P i o) = Q i o) (hp : ∀ i o, (p i o).map φ = q i o)
    (k : Fin (n + 1)) (o : I k) :
    map φ (polynomialChainPrefix (fun i o => Polynomial.aeval (P i o) (p i o)) k o) =
      polynomialChainPrefix (fun i o => Polynomial.aeval (Q i o) (q i o)) k o := by
  rw [map_polynomialChainPrefix]
  refine congrArg (fun R => polynomialChainPrefix R k o) (funext fun i => funext fun a => ?_)
  rw [Function.comp_apply, Polynomial.map_aeval_eq_aeval_map (map_comp_C φ).symm, hP, hp]

/-- Transporting `polynomialChain` along a ring homomorphism transports each layer model. -/
@[simp] theorem map_polynomialChain {L : Type*} [CommSemiring L] (φ : K →+* L)
    (P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K) (o : I (Fin.last n)) :
    map φ (polynomialChain P o) = polynomialChain (fun i => map φ ∘ P i) o :=
  map_polynomialChainPrefix φ P (Fin.last n) o

end TauCeti.Neuromanifold
