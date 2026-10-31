/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Neuromanifold.MLP.Basic
public import TauCeti.Geometry.Neuromanifold.Polynomial.Constructors

/-!
# MLPs with polynomial activations are jointly polynomial models

For an MLP specification `A`, the affine parameters are indexed by the finite type
`A.ParameterIndex`: for each layer `i : Fin L`, one index for each entry of the weight matrix
`Wᵢ₊₁` and one for each coordinate of the bias `bᵢ₊₁`. The bias-free parameters are indexed by
`A.WeightIndex`, the matrix entries alone. The equivalences `MLPSpec.parameterEquiv` and
`MLPSpec.weightEquiv` reassemble the parameter tuples from these coordinates, layer by layer
through `denseParameterEquiv` and `linearParameterEquiv`. The index types are finite, with
`∑ i, (dᵢ₊₁ dᵢ + dᵢ₊₁)` and `∑ i, dᵢ₊₁ dᵢ` elements, so `Fintype.equivFin` numbers them as
`Fin p` for that count `p`.

When every hidden activation of `A` is a polynomial function `t ↦ (q j).eval t`, the prefix
evaluations of `A` are polynomial jointly in the parameter coordinates and the input:
`MLPSpec.polynomialPrefix A q` follows the prefix recursion `h₀ = x`,
`hᵢ₊₁ = σᵢ₊₁ (Wᵢ₊₁ hᵢ + bᵢ₊₁)` with polynomials in place of functions, where the activation
polynomial of each layer is `MLPSpec.layerPolynomial q`: `q` on hidden layers and `X` on the
affine output layer. Its last layer `MLPSpec.polynomialRealize A q` is a jointly polynomial
tuple realizing `A.realize` after `A.parameterEquiv`, and substituting zero for every bias
variable gives `MLPSpec.polynomialRealizeWeights A q`, realizing `A.realizeWeights` after
`A.weightEquiv`. Thus the coefficient extraction, uniform input-degree bound, and faithful
coefficient presentation of `TauCeti.Geometry.Neuromanifold.Polynomial.Presentation` apply to
these networks. The identity-activation and monomial specifications are the cases
`q = X` and `q j = X ^ r j`.

The jointly polynomial setting follows Marchetti–Shahverdi–Mereta–Trager–Kohn,
*Algebra Unveils Deep Learning — An Invitation to Neuroalgebraic Geometry*,
[arXiv:2501.18915v2](https://arxiv.org/abs/2501.18915v2), §3.1. The bias-free monomial
networks are those of Finkel–Rodriguez–Wu–Yahl, *Activation degree thresholds and
expressiveness of polynomial neural networks*,
[arXiv:2408.04569v4](https://arxiv.org/abs/2408.04569v4), Definition 1.
-/

public section

noncomputable section

namespace TauCeti.Neuromanifold

namespace MLPSpec

open MvPolynomial

variable {K : Type*} {L : ℕ}

/-! ### Parameter coordinates -/

section ParameterCoordinates

/-- The coordinates of the affine parameters of `A`: for the layer at `i`, a matrix position
`(o, j)` of `Wᵢ₊₁` or an output coordinate `o` of `bᵢ₊₁`. -/
abbrev ParameterIndex (A : MLPSpec K L) : Type :=
  Σ i : Fin L, Fin (A.width i.succ) × Fin (A.width i.castSucc) ⊕ Fin (A.width i.succ)

/-- The coordinates of the bias-free parameters of `A`: for the layer at `i`, a matrix position
`(o, j)` of `Wᵢ₊₁`. -/
abbrev WeightIndex (A : MLPSpec K L) : Type :=
  Σ i : Fin L, Fin (A.width i.succ) × Fin (A.width i.castSucc)

/-- The number of affine parameters of `A`: the sizes of all weight matrices and biases. -/
theorem card_parameterIndex (A : MLPSpec K L) :
    Fintype.card A.ParameterIndex =
      ∑ i : Fin L, (A.width i.succ * A.width i.castSucc + A.width i.succ) := by
  simp

/-- The number of bias-free parameters of `A`: the sizes of all weight matrices. -/
theorem card_weightIndex (A : MLPSpec K L) :
    Fintype.card A.WeightIndex = ∑ i : Fin L, A.width i.succ * A.width i.castSucc := by
  simp

/-- The affine parameters of `A`, read off from their coordinates layer by layer. -/
def parameterEquiv (A : MLPSpec K L) : (A.ParameterIndex → K) ≃ A.Parameters :=
  (Equiv.piCurry fun _ _ => K).trans (Equiv.piCongrRight fun _ => denseParameterEquiv K _ _)

/-- The bias-free parameters of `A`, read off from their coordinates layer by layer. -/
def weightEquiv (A : MLPSpec K L) : (A.WeightIndex → K) ≃ A.Weights :=
  (Equiv.piCurry fun _ _ => K).trans (Equiv.piCongrRight fun _ => linearParameterEquiv K _ _)

/-- The weight matrices read off from affine parameter coordinates. -/
@[simp] theorem parameterEquiv_apply_fst (A : MLPSpec K L) (v : A.ParameterIndex → K)
    (i : Fin L) (o : Fin (A.width i.succ)) (j : Fin (A.width i.castSucc)) :
    (A.parameterEquiv v i).1 o j = v ⟨i, .inl (o, j)⟩ := by
  simp [parameterEquiv, Sigma.curry]

/-- The biases read off from affine parameter coordinates. -/
@[simp] theorem parameterEquiv_apply_snd (A : MLPSpec K L) (v : A.ParameterIndex → K)
    (i : Fin L) (o : Fin (A.width i.succ)) :
    (A.parameterEquiv v i).2 o = v ⟨i, .inr o⟩ := by
  simp [parameterEquiv, Sigma.curry]

/-- The affine parameter coordinate at a matrix position is the corresponding weight. -/
@[simp] theorem parameterEquiv_symm_apply_inl (A : MLPSpec K L) (θ : A.Parameters) (i : Fin L)
    (o : Fin (A.width i.succ)) (j : Fin (A.width i.castSucc)) :
    A.parameterEquiv.symm θ ⟨i, .inl (o, j)⟩ = (θ i).1 o j := by
  simp [parameterEquiv, Sigma.uncurry]

/-- The affine parameter coordinate at a bias position is the corresponding bias. -/
@[simp] theorem parameterEquiv_symm_apply_inr (A : MLPSpec K L) (θ : A.Parameters) (i : Fin L)
    (o : Fin (A.width i.succ)) :
    A.parameterEquiv.symm θ ⟨i, .inr o⟩ = (θ i).2 o := by
  simp [parameterEquiv, Sigma.uncurry]

/-- The weight matrices read off from bias-free parameter coordinates. -/
@[simp] theorem weightEquiv_apply (A : MLPSpec K L) (v : A.WeightIndex → K) (i : Fin L)
    (o : Fin (A.width i.succ)) (j : Fin (A.width i.castSucc)) :
    A.weightEquiv v i o j = v ⟨i, (o, j)⟩ := by
  simp [weightEquiv, Sigma.curry]

/-- The bias-free parameter coordinate at a matrix position is the corresponding weight. -/
@[simp] theorem weightEquiv_symm_apply (A : MLPSpec K L) (w : A.Weights) (i : Fin L)
    (o : Fin (A.width i.succ)) (j : Fin (A.width i.castSucc)) :
    A.weightEquiv.symm w ⟨i, (o, j)⟩ = w i o j := by
  simp [weightEquiv, Sigma.uncurry]

end ParameterCoordinates

/-! ### Polynomial prefixes -/

section Polynomial

variable [CommSemiring K]

/-- The activation polynomial of the layer at `i : Fin L`, which produces layer `i + 1`: the
hidden polynomial `q` when `i + 1 < L`, and `X` on the affine output layer. -/
def layerPolynomial (q : Fin (L - 1) → Polynomial K) (i : Fin L) : Polynomial K :=
  if h : i.val + 1 < L then q ⟨i.val, by omega⟩ else Polynomial.X

/-- In depth `L + 1`, the layer at `i : Fin L` is hidden and has activation polynomial `q i`. -/
@[simp] theorem layerPolynomial_castSucc (q : Fin L → Polynomial K) (i : Fin L) :
    layerPolynomial (L := L + 1) q i.castSucc = q i := by
  simp [layerPolynomial]

/-- In depth `L + 1`, the output layer has activation polynomial `X`. -/
@[simp] theorem layerPolynomial_last (q : Fin L → Polynomial K) :
    layerPolynomial (L := L + 1) q (Fin.last L) = Polynomial.X := by
  simp [layerPolynomial]

/-- Identity hidden activation polynomials give `X` on every layer. -/
@[simp] theorem layerPolynomial_X (i : Fin L) :
    layerPolynomial (fun _ => (Polynomial.X : Polynomial K)) i = Polynomial.X := by
  unfold layerPolynomial
  split <;> rfl

/-- If the hidden activations of `A` evaluate the polynomials `q`, then every layer of `A`
evaluates its activation polynomial. -/
theorem layerActivation_eq_eval_layerPolynomial (A : MLPSpec K L)
    {q : Fin (L - 1) → Polynomial K} (hq : ∀ j t, A.activation j t = (q j).eval t) (i : Fin L)
    (t : K) : A.layerActivation i t = (layerPolynomial q i).eval t := by
  by_cases h : i.val + 1 < L
  · simp [A.layerActivation_of_lt i h, hq, layerPolynomial, h]
  · simp [A.layerActivation_of_val_add_one_eq i (by omega), layerPolynomial, h]

/-- The prefix polynomials of `A` with hidden activation polynomials `q`, in the affine parameter
coordinates and the input variables: `h₀ = x` and `hᵢ₊₁ = pᵢ (Wᵢ₊₁ hᵢ + bᵢ₊₁)`
coordinatewise, where `pᵢ` is `layerPolynomial q i`. -/
def polynomialPrefix (A : MLPSpec K L) (q : Fin (L - 1) → Polynomial K) :
    (i : Fin (L + 1)) → Fin (A.width i) → MvPolynomial (A.ParameterIndex ⊕ Fin (A.width 0)) K :=
  Fin.induction (fun j => X (.inr j)) fun i h o =>
    Polynomial.aeval (∑ j, X (.inl ⟨i, .inl (o, j)⟩) * h j + X (.inl ⟨i, .inr o⟩))
      (layerPolynomial q i)

/-- The zeroth prefix polynomials are the input variables. -/
@[simp] theorem polynomialPrefix_zero (A : MLPSpec K L) (q : Fin (L - 1) → Polynomial K) :
    A.polynomialPrefix q 0 = fun j => X (.inr j) :=
  Fin.induction_zero ..

/-- The prefix recursion of the polynomial prefixes. -/
@[simp] theorem polynomialPrefix_succ (A : MLPSpec K L) (q : Fin (L - 1) → Polynomial K)
    (i : Fin L) :
    A.polynomialPrefix q i.succ = fun o =>
      Polynomial.aeval
        (∑ j, X (.inl ⟨i, .inl (o, j)⟩) * A.polynomialPrefix q i.castSucc j +
          X (.inl ⟨i, .inr o⟩))
        (layerPolynomial q i) :=
  Fin.induction_succ ..

/-- If the hidden activations of `A` evaluate the polynomials `q`, then evaluating the prefix
polynomials at parameter coordinates `v` and input `x` gives the prefix evaluation of `A` at the
parameters assembled from `v`. -/
theorem eval_polynomialPrefix (A : MLPSpec K L) {q : Fin (L - 1) → Polynomial K}
    (hq : ∀ j t, A.activation j t = (q j).eval t) (v : A.ParameterIndex → K)
    (x : Fin (A.width 0) → K) (i : Fin (L + 1)) (o : Fin (A.width i)) :
    eval (Sum.elim v x) (A.polynomialPrefix q i o) = A.evalPrefix (A.parameterEquiv v) x i o := by
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
    simp only [polynomialPrefix_succ, evalPrefix_succ]
    rw [← aeval_eq_eval, ← Polynomial.aeval_algHom_apply, Polynomial.coe_aeval_eq_eval,
      A.layerActivation_eq_eval_layerPolynomial hq]
    simp [aeval_eq_eval, ih, Matrix.mulVec, dotProduct]

/-- The jointly polynomial tuple of `A` with hidden activation polynomials `q`: the output-layer
prefix polynomials, in the affine parameter coordinates and the input variables. -/
def polynomialRealize (A : MLPSpec K L) (q : Fin (L - 1) → Polynomial K) :
    Fin (A.width (Fin.last L)) → MvPolynomial (A.ParameterIndex ⊕ Fin (A.width 0)) K :=
  A.polynomialPrefix q (Fin.last L)

/-- The jointly polynomial tuple of `A` is its output-layer prefix polynomials. -/
theorem polynomialRealize_def (A : MLPSpec K L) (q : Fin (L - 1) → Polynomial K) :
    A.polynomialRealize q = A.polynomialPrefix q (Fin.last L) := (rfl)

/-- An MLP whose hidden activations evaluate the polynomials `q` is a jointly polynomial model:
its polynomial tuple realizes `A.realize` on the parameters assembled from their coordinates. -/
theorem polynomialRealization_polynomialRealize (A : MLPSpec K L)
    {q : Fin (L - 1) → Polynomial K} (hq : ∀ j t, A.activation j t = (q j).eval t) :
    polynomialRealization (A.polynomialRealize q) = A.realize ∘ A.parameterEquiv := by
  funext v x o
  rw [polynomialRealization_apply, Function.comp_apply, realize_def, polynomialRealize_def]
  exact A.eval_polynomialPrefix hq v x _ o

/-- The polynomial tuple of `A` realizes the same functions as `A`. -/
theorem realizedFunctions_polynomialRealize (A : MLPSpec K L)
    {q : Fin (L - 1) → Polynomial K} (hq : ∀ j t, A.activation j t = (q j).eval t) :
    realizedFunctions (polynomialRealization (A.polynomialRealize q)) =
      realizedFunctions A.realize := by
  rw [A.polynomialRealization_polynomialRealize hq, realizedFunctions_def, realizedFunctions_def,
    A.parameterEquiv.surjective.range_comp]

/-- The substitution of bias-free parameter coordinates into affine parameter coordinates:
each weight variable is kept, and each bias variable is replaced by zero. -/
def zeroBiasSubstitution (A : MLPSpec K L) : A.ParameterIndex → MvPolynomial A.WeightIndex K
  | ⟨i, .inl p⟩ => X ⟨i, p⟩
  | ⟨_, .inr _⟩ => 0

/-- The zero-bias substitution keeps each weight variable. -/
@[simp] theorem zeroBiasSubstitution_inl (A : MLPSpec K L) (i : Fin L)
    (p : Fin (A.width i.succ) × Fin (A.width i.castSucc)) :
    A.zeroBiasSubstitution ⟨i, .inl p⟩ = X ⟨i, p⟩ := by
  simp [zeroBiasSubstitution]

/-- The zero-bias substitution replaces each bias variable by zero. -/
@[simp] theorem zeroBiasSubstitution_inr (A : MLPSpec K L) (i : Fin L) (o : Fin (A.width i.succ)) :
    A.zeroBiasSubstitution ⟨i, .inr o⟩ = 0 := by
  simp [zeroBiasSubstitution]

/-- Evaluating the zero-bias substitution at bias-free coordinates gives the coordinates of the
zero-bias embedding. -/
theorem eval_zeroBiasSubstitution (A : MLPSpec K L) (v : A.WeightIndex → K) :
    (fun k => eval v (A.zeroBiasSubstitution k)) =
      A.parameterEquiv.symm (A.zeroBias (A.weightEquiv v)) := by
  funext ⟨i, k⟩
  rcases k with ⟨o, j⟩ | o <;> simp

/-- The bias-free jointly polynomial tuple of `A` with hidden activation polynomials `q`: the
tuple `A.polynomialRealize q` with every bias variable replaced by zero. -/
def polynomialRealizeWeights (A : MLPSpec K L) (q : Fin (L - 1) → Polynomial K) :
    Fin (A.width (Fin.last L)) → MvPolynomial (A.WeightIndex ⊕ Fin (A.width 0)) K :=
  polynomialReparametrize A.zeroBiasSubstitution (A.polynomialRealize q)

/-- The bias-free jointly polynomial tuple of `A` substitutes zero for the bias variables. -/
theorem polynomialRealizeWeights_def (A : MLPSpec K L) (q : Fin (L - 1) → Polynomial K) :
    A.polynomialRealizeWeights q =
      polynomialReparametrize A.zeroBiasSubstitution (A.polynomialRealize q) := (rfl)

/-- A bias-free MLP whose hidden activations evaluate the polynomials `q` is a jointly
polynomial model: its bias-free polynomial tuple realizes `A.realizeWeights` on the weights
assembled from their coordinates. -/
theorem polynomialRealization_polynomialRealizeWeights (A : MLPSpec K L)
    {q : Fin (L - 1) → Polynomial K} (hq : ∀ j t, A.activation j t = (q j).eval t) :
    polynomialRealization (A.polynomialRealizeWeights q) = A.realizeWeights ∘ A.weightEquiv := by
  funext v
  simp only [polynomialRealizeWeights, polynomialRealization_polynomialReparametrize]
  rw [eval_zeroBiasSubstitution, A.polynomialRealization_polynomialRealize hq]
  simp [realizeWeights_def]

/-- The bias-free polynomial tuple of `A` realizes the same functions as `A` on bias-free
parameters. -/
theorem realizedFunctions_polynomialRealizeWeights (A : MLPSpec K L)
    {q : Fin (L - 1) → Polynomial K} (hq : ∀ j t, A.activation j t = (q j).eval t) :
    realizedFunctions (polynomialRealization (A.polynomialRealizeWeights q)) =
      realizedFunctions A.realizeWeights := by
  rw [A.polynomialRealization_polynomialRealizeWeights hq, realizedFunctions_def,
    realizedFunctions_def, A.weightEquiv.surjective.range_comp]

/-- A linear network, with identity hidden activations, is a jointly polynomial model whose
hidden activation polynomials are `X`. -/
theorem polynomialRealization_polynomialRealize_linear (d : Fin (L + 1) → ℕ) :
    polynomialRealization ((linear d : MLPSpec K L).polynomialRealize fun _ => Polynomial.X) =
      (linear d).realize ∘ (linear d).parameterEquiv :=
  (linear d).polynomialRealization_polynomialRealize fun _ _ => by simp

/-- A bias-free monomial MLP, with hidden activations `t ↦ t ^ r j`, is a jointly polynomial
model whose hidden activation polynomials are `X ^ r j`. -/
theorem polynomialRealization_polynomialRealizeWeights_monomial (d : Fin (L + 1) → ℕ)
    (r : Fin (L - 1) → ℕ) :
    polynomialRealization
        ((monomial d r : MLPSpec K L).polynomialRealizeWeights fun j => Polynomial.X ^ r j) =
      (monomial d r).realizeWeights ∘ (monomial d r).weightEquiv :=
  (monomial d r).polynomialRealization_polynomialRealizeWeights fun _ _ => by simp

end Polynomial

end MLPSpec

end TauCeti.Neuromanifold
