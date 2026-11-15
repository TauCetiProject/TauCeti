/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Fin.Basic
public import TauCeti.Geometry.Neuromanifold.Chain
public import TauCeti.Geometry.Neuromanifold.Polynomial.Homogeneous
public import TauCeti.Geometry.Neuromanifold.Polynomial.Map

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
faithful bounded-degree and homogeneous coefficient presentations, and scalar transport of the
jointly polynomial interface.

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
  Fin.induction (fun a => X (Sum.inr a)) fun i prev o =>
    bind₁ (Sum.elim (fun w => X (Sum.inl ⟨i, w⟩)) prev) (P i o)

/-- The zeroth prefix of a chain of polynomial models is the tuple of input variables. -/
@[simp] theorem polynomialChainPrefix_zero
    (P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K) :
    polynomialChainPrefix P 0 = fun a => X (Sum.inr a) :=
  Fin.induction_zero ..

/-- Each step of `polynomialChainPrefix` substitutes the preceding prefix for the layer's inputs
and tags the layer's parameter variables with its index. -/
@[simp] theorem polynomialChainPrefix_succ
    (P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K) (i : Fin n) (o : I i.succ) :
    polynomialChainPrefix P i.succ o =
      bind₁ (Sum.elim (fun w => X (Sum.inl ⟨i, w⟩)) (polynomialChainPrefix P i.castSucc))
        (P i o) := by
  simp only [polynomialChainPrefix, Fin.induction_succ]

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
theorem polynomialChainPrefix_succ_eq_rename_polynomialCompose
    (P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K) (i : Fin n) (o : I i.succ) :
    polynomialChainPrefix P i.succ o =
      rename (Sum.map (Sum.elim id (Sigma.mk i)) id)
        (polynomialCompose (polynomialChainPrefix P i.castSucc) (P i) o) := by
  rw [polynomialChainPrefix_succ, polynomialCompose_apply, rename_bind₁]
  refine congrArg (fun F => bind₁ F (P i o)) (funext fun x => ?_)
  rcases x with w | a
  · simp
  · simp only [Sum.elim_inr, rename_rename]
    have hid :
        Sum.map (Sum.elim id (Sigma.mk (β := W) i)) (id : I 0 → I 0) ∘ Sum.map Sum.inl id =
          id := by
      funext y
      cases y <;> rfl
    rw [hid, rename_id_apply]

/-- Every prefix `polynomialChainPrefix P k` is the `k.val`-step dependent left fold `Fin.dfoldl`
of layerwise polynomial substitution, starting from the input variables. -/
theorem polynomialChainPrefix_eq_dfoldl
    (P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K) (k : Fin (n + 1)) :
    polynomialChainPrefix P k =
      Fin.dfoldl k.val (fun j => I (Fin.castLE k.isLt j) → MvPolynomial ((Σ i, W i) ⊕ I 0) K)
        (fun j prev o =>
          bind₁ (Sum.elim (fun w => X (Sum.inl ⟨Fin.castLE (Nat.le_of_lt_succ k.isLt) j, w⟩)) prev)
            (P (Fin.castLE (Nat.le_of_lt_succ k.isLt) j) o))
        (fun a => X (Sum.inr a)) := by
  induction k using Fin.induction with
  | zero =>
    exact (polynomialChainPrefix_zero P).trans
      (Fin.dfoldl_zero
        (α := fun j => I (Fin.castLE (0 : Fin (n + 1)).isLt j) →
          MvPolynomial ((Σ i, W i) ⊕ I 0) K)
        _ (fun a => X (Sum.inr a))).symm
  | succ i ih =>
    have hsucc : polynomialChainPrefix P i.succ = fun o =>
        bind₁ (Sum.elim (fun w => X (Sum.inl ⟨i, w⟩)) (polynomialChainPrefix P i.castSucc))
          (P i o) := funext (polynomialChainPrefix_succ P i)
    rw [hsucc, ih]
    exact (Fin.dfoldl_succ_last
      (α := fun j => I (Fin.castLE i.succ.isLt j) → MvPolynomial ((Σ i, W i) ⊕ I 0) K)
      (fun j prev o =>
        bind₁ (Sum.elim (fun w => X (Sum.inl ⟨Fin.castLE (Nat.le_of_lt_succ i.succ.isLt) j, w⟩))
            prev)
          (P (Fin.castLE (Nat.le_of_lt_succ i.succ.isLt) j) o))
      (fun a => X (Sum.inr a))).symm

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
        (fun i prev o => bind₁ (Sum.elim (fun w => X (Sum.inl ⟨i, w⟩)) prev) (P i o))
        (fun a => X (Sum.inr a)) :=
  polynomialChainPrefix_eq_dfoldl P (Fin.last n)

/-- The empty chain of polynomial models is the tuple of input variables. -/
@[simp] theorem polynomialChain_zero {I : Fin 1 → Type*} {W : Fin 0 → Type*}
    (P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K) :
    polynomialChain P = fun a => X (Sum.inr a) :=
  polynomialChainPrefix_zero P

/-- A one-layer chain of polynomial models renames the single layer's parameter variables into
`Σ i : Fin 1, W i`. -/
theorem polynomialChain_one {I : Fin 2 → Type*} {W : Fin 1 → Type*}
    (P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K) :
    polynomialChain P = fun o => rename (Sum.map (Sigma.mk 0) id) (P 0 o) := by
  funext o
  change polynomialChainPrefix P (0 : Fin 1).succ o = _
  rw [polynomialChainPrefix_succ,
    show polynomialChainPrefix P (0 : Fin 1).castSucc = fun a => X (Sum.inr a) from
      polynomialChainPrefix_zero P,
    rename_eq_aeval (Sum.map (Sigma.mk 0) id), aeval_eq_bind₁]
  refine congrArg (fun F => bind₁ F (P 0 o)) (funext fun x => ?_)
  cases x <;> rfl

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
    change polynomialChainPrefix P 0 o = _
    rw [polynomialChainPrefix_zero, polynomialChainPrefix_zero, rename_X]
    rfl
  | succ i ih =>
    change polynomialChainPrefix P i.castSucc.succ o = _
    rw [polynomialChainPrefix_succ, polynomialChainPrefix_succ, rename_bind₁]
    refine congrArg (fun F => bind₁ F (P i.castSucc o)) (funext fun x => ?_)
    rcases x with w | a
    · simp only [Sum.elim_inl]
      rw [rename_X]
      rfl
    · simp only [Sum.elim_inr]
      exact ih a

/-- Every positive prefix of a nonempty chain is the binary composition `polynomialCompose` of the
first layer `P 0` with the corresponding prefix of the tail chain, after folding the first-layer
and tail parameter variables into `Σ i, W i`. -/
theorem polynomialChainPrefix_succ_eq_polynomialCompose
    {I : Fin (n + 2) → Type*} {W : Fin (n + 1) → Type*}
    (P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K) (k : Fin (n + 1)) (o : I k.succ) :
    polynomialChainPrefix P k.succ o =
      rename (Sum.map (Sum.elim (Sigma.mk 0) (fun p => ⟨p.1.succ, p.2⟩)) id)
        (polynomialCompose (P 0)
          (polynomialChainPrefix (I := fun i => I i.succ) (fun i => P i.succ) k) o) := by
  induction k using Fin.induction with
  | zero =>
    rw [polynomialChainPrefix_succ, polynomialChainPrefix_zero, polynomialCompose_apply]
    simp only [bind₁_X_right, Sum.elim_inr, rename_rename]
    rw [rename_eq_aeval (Sum.map (Sum.elim (Sigma.mk 0) _) id ∘ Sum.map Sum.inl id),
      aeval_eq_bind₁]
    refine congrArg (fun F => bind₁ F (P 0 o)) (funext fun x => ?_)
    cases x <;> rfl
  | succ i ih =>
    rw [polynomialChainPrefix_succ, polynomialCompose_apply, polynomialChainPrefix_succ,
      bind₁_bind₁, rename_bind₁]
    refine congrArg (fun F => bind₁ F (P i.succ o)) (funext fun x => ?_)
    rcases x with w | a
    · simp only [Sum.elim_inl, bind₁_X_right]
      rw [rename_X]
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
  funext (polynomialChainPrefix_succ_eq_polynomialCompose P (Fin.last n))

/-- Split off the last layer of `polynomialChain` as a binary `polynomialCompose`, folding the
prefix and last-layer parameter variables into `Σ i, W i`. -/
theorem polynomialChain_succ_last {I : Fin (n + 2) → Type*} {W : Fin (n + 1) → Type*}
    (P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K) :
    polynomialChain P = fun o =>
      rename (Sum.map (Sum.elim (fun p => ⟨p.1.castSucc, p.2⟩) (Sigma.mk (Fin.last n))) id)
        (polynomialCompose
          (polynomialChain (I := fun i => I i.castSucc) (fun i => P i.castSucc))
          (P (Fin.last n)) o) := by
  funext o
  change polynomialChainPrefix P (Fin.last n).succ o = _
  rw [polynomialChainPrefix_succ_eq_rename_polynomialCompose, polynomialCompose_apply,
    polynomialCompose_apply, rename_bind₁, rename_bind₁]
  refine congrArg (fun F => bind₁ F (P (Fin.last n) o)) (funext fun x => ?_)
  rcases x with w | a
  · simp only [Sum.elim_inl]
    rw [rename_X, rename_X]
    rfl
  · simp only [Sum.elim_inr, polynomialChain_def]
    refine (rename_rename _ _ _).trans ?_
    refine ((congrArg _ (polynomialChainPrefix_castSucc P (Fin.last n) a)).trans
      (rename_rename _ _ _)).trans ?_
    refine (congrArg (fun f => rename f _) ?_).trans (rename_rename _ _ _).symm
    funext y
    rcases y with ⟨j, v⟩ | x₀ <;> rfl

/-! ### Evaluation and neuromanifolds -/

/-- Prefix `0` of `polynomialChainPrefix` realizes the identity on inputs at every parameter. -/
theorem polynomialRealization_polynomialChainPrefix_zero
    (P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K) :
    polynomialRealization (polynomialChainPrefix P 0) = fun _ x => x := by
  funext w x a
  simp

/-- Step `i + 1` of `polynomialChainPrefix` evaluates layer `P i` on the output of step `i`, using
the layer's slice `v ↦ w ⟨i, v⟩` of parameter coordinates. -/
@[simp] theorem polynomialRealization_polynomialChainPrefix_succ
    (P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K) (i : Fin n) (w : (Σ j, W j) → K)
    (x : I 0 → K) :
    polynomialRealization (polynomialChainPrefix P i.succ) w x =
      polynomialRealization (P i) (fun v => w ⟨i, v⟩)
        (polynomialRealization (polynomialChainPrefix P i.castSucc) w x) := by
  funext o
  have hstep : polynomialChainPrefix P i.succ =
      fun k => rename (Sum.map (Sum.elim id (Sigma.mk i)) id)
        (polynomialCompose (polynomialChainPrefix P i.castSucc) (P i) k) :=
    funext (polynomialChainPrefix_succ_eq_rename_polynomialCompose P i)
  rw [hstep]
  simp only [polynomialRealization_rename_sumMap, polynomialRealization_polynomialCompose,
    Function.comp_apply, compose_apply_apply]
  rfl

/-- Evaluating `polynomialChainPrefix P k` agrees with the `k.val`-step dependent left fold of the
layer realization maps. -/
theorem polynomialRealization_polynomialChainPrefix_eq_dfoldl
    (P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K) (w : (Σ i, W i) → K)
    (x : I 0 → K) (k : Fin (n + 1)) :
    polynomialRealization (polynomialChainPrefix P k) w x =
      Fin.dfoldl k.val (fun j => I (Fin.castLE k.isLt j) → K)
        (fun j => polynomialRealization (P (Fin.castLE (Nat.le_of_lt_succ k.isLt) j))
          (fun v => w ⟨Fin.castLE (Nat.le_of_lt_succ k.isLt) j, v⟩))
        x := by
  induction k using Fin.induction with
  | zero =>
    exact (congrFun (congrFun (polynomialRealization_polynomialChainPrefix_zero P) w) x).trans
      (Fin.dfoldl_zero (α := fun j => I (Fin.castLE (0 : Fin (n + 1)).isLt j) → K) _ x).symm
  | succ i ih =>
    rw [polynomialRealization_polynomialChainPrefix_succ, ih]
    exact (Fin.dfoldl_succ_last (α := fun j => I (Fin.castLE i.succ.isLt j) → K)
      (fun j => polynomialRealization (P (Fin.castLE (Nat.le_of_lt_succ i.succ.isLt) j))
        (fun v => w ⟨Fin.castLE (Nat.le_of_lt_succ i.succ.isLt) j, v⟩))
      x).symm

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
  exact polynomialRealization_polynomialChainPrefix_eq_dfoldl P w x (Fin.last n)

/-- Composing a finite chain of polynomial models by substitution realizes the same functions as
composing their realization maps with `chain`. -/
theorem realizedFunctions_polynomialChain
    (P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K) :
    realizedFunctions (polynomialRealization (polynomialChain P)) =
      realizedFunctions (chain (X := fun k => I k → K) fun i => polynomialRealization (P i)) := by
  rw [polynomialRealization_polynomialChain, realizedFunctions_def, realizedFunctions_def,
    (Equiv.piCurry fun _ _ => K).surjective.range_comp]

/-! ### Input polynomials, reparametrization, homogeneity, and scalar transport -/

/-- The collected input polynomials at prefix `0` are the initial input variables. -/
theorem inputPolynomial_polynomialChainPrefix_zero
    (P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K) (a : I 0) :
    inputPolynomial (polynomialChainPrefix P 0) a = X a :=
  (congrArg (fun Q => inputPolynomial Q a) (polynomialChainPrefix_zero P)).trans
    (inputPolynomial_X_inr id a)

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
  have hstep : polynomialChainPrefix P i.succ =
      fun k => rename (Sum.map (Sum.elim id (Sigma.mk i)) id)
        (polynomialCompose (polynomialChainPrefix P i.castSucc) (P i) k) :=
    funext (polynomialChainPrefix_succ_eq_rename_polynomialCompose P i)
  rw [hstep, inputPolynomial_rename_sumMap, inputPolynomial_polynomialCompose, hom_eval₂]
  refine congrArg₂ (fun f g => eval₂ f g (inputPolynomial (P i) o)) ?_ (funext fun a => ?_)
  · ext w <;> simp
  · simp only [map_map]
    convert map_id (inputPolynomial (polynomialChainPrefix P i.castSucc) a)
    ext w <;> simp

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
      polynomialReparametrize_apply, bind₁_bind₁, bind₁_bind₁]
    refine congrArg (fun F => bind₁ F (P i o)) (funext fun x => ?_)
    rcases x with w | a
    · simp only [Sum.elim_inl, bind₁_X_right, rename_rename, bind₁_rename]
      rw [rename_eq_aeval, aeval_eq_bind₁]
      rfl
    · simp only [Sum.elim_inr, bind₁_X_right, ← polynomialReparametrize_apply]
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
    rw [inputPolynomial_polynomialChainPrefix_zero]
    exact (isHomogeneous_X _ a).totalDegree_le
  | succ i ih =>
    have hstep : polynomialChainPrefix P i.succ =
        fun k => rename (Sum.map (Sum.elim id (Sigma.mk i)) id)
          (polynomialCompose (polynomialChainPrefix P i.castSucc) (P i) k) :=
      funext (polynomialChainPrefix_succ_eq_rename_polynomialCompose P i)
    rw [hstep, Fin.partialProd_succ]
    exact (polynomialInputDegree_rename_sumMap_le _ _).trans <|
      (polynomialInputDegree_polynomialCompose_le _ _).trans (Nat.mul_le_mul_right _ ih)

/-- With finite coordinate types, the uniform input-degree bound of `polynomialChain P` is at most
the product of the layer input-degree bounds. -/
theorem polynomialInputDegree_polynomialChain_le [∀ k, Fintype (I k)]
    (P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K) :
    polynomialInputDegree (polynomialChain P) ≤ ∏ i, polynomialInputDegree (P i) := by
  simpa only [polynomialChain_def, Fin.partialProd_last] using
    polynomialInputDegree_polynomialChainPrefix_le P (Fin.last n)

/-- If each layer `P i` is homogeneous in its inputs of degree `d i`, then prefix `k` of
`polynomialChainPrefix P` is homogeneous in the initial inputs of degree `Fin.partialProd d k`. -/
theorem isHomogeneous_inputPolynomial_polynomialChainPrefix
    {P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K} {d : Fin n → ℕ}
    (hP : ∀ i o, (inputPolynomial (P i) o).IsHomogeneous (d i)) (k : Fin (n + 1)) (o : I k) :
    (inputPolynomial (polynomialChainPrefix P k) o).IsHomogeneous (Fin.partialProd d k) := by
  induction k using Fin.induction with
  | zero =>
    rw [inputPolynomial_polynomialChainPrefix_zero, Fin.partialProd_zero]
    exact isHomogeneous_X _ o
  | succ i ih =>
    have hstep : polynomialChainPrefix P i.succ =
        fun k => rename (Sum.map (Sum.elim id (Sigma.mk i)) id)
          (polynomialCompose (polynomialChainPrefix P i.castSucc) (P i) k) :=
      funext (polynomialChainPrefix_succ_eq_rename_polynomialCompose P i)
    rw [hstep, Fin.partialProd_succ]
    exact isHomogeneous_inputPolynomial_rename_sumMap _
      (isHomogeneous_inputPolynomial_polynomialCompose ih (hP i)) o

/-- If each layer `P i` is homogeneous in its inputs of degree `d i`, then `polynomialChain P` is
homogeneous in the initial inputs of degree `∏ i, d i`. -/
theorem isHomogeneous_inputPolynomial_polynomialChain
    {P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K} {d : Fin n → ℕ}
    (hP : ∀ i o, (inputPolynomial (P i) o).IsHomogeneous (d i)) (o : I (Fin.last n)) :
    (inputPolynomial (polynomialChain P) o).IsHomogeneous (∏ i, d i) := by
  simpa only [polynomialChain_def, Fin.partialProd_last] using
    isHomogeneous_inputPolynomial_polynomialChainPrefix hP (Fin.last n) o

/-- Transporting `polynomialChainPrefix` along a ring homomorphism transports each layer model. -/
@[simp] theorem map_polynomialChainPrefix {L : Type*} [CommSemiring L] (φ : K →+* L)
    (P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K) (k : Fin (n + 1)) (o : I k) :
    map φ (polynomialChainPrefix P k o) =
      polynomialChainPrefix (fun i => map φ ∘ P i) k o := by
  induction k using Fin.induction with
  | zero => simp
  | succ i ih =>
    rw [polynomialChainPrefix_succ, polynomialChainPrefix_succ, map_bind₁, Function.comp_apply]
    refine congrArg (fun F => bind₁ F _) (funext fun x => ?_)
    rcases x with w | a
    · simp
    · exact ih a

/-- Transporting `polynomialChain` along a ring homomorphism transports each layer model. -/
@[simp] theorem map_polynomialChain {L : Type*} [CommSemiring L] (φ : K →+* L)
    (P : ∀ i, I i.succ → MvPolynomial (W i ⊕ I i.castSucc) K) (o : I (Fin.last n)) :
    map φ (polynomialChain P o) = polynomialChain (fun i => map φ ∘ P i) o :=
  map_polynomialChainPrefix φ P (Fin.last n) o

end TauCeti.Neuromanifold
