/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Representability.LabeledGraph
public import Mathlib.Combinatorics.SimpleGraph.Sum
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Graph parameters, connection matrices and reflection positivity

A graph parameter assigns a real number to every finite simple graph.  Its connection matrices are
the matrices of its values on the gluings of a finite family of `k`-labeled graphs; a parameter is
reflection positive when all of them are positive semidefinite.  Together with multiplicativity
over disjoint unions and normalization at the one-vertex graph, these are the structural conditions
of the Lovász–Szegedy representability theorem.

## Main definitions

* `TauCeti.DenseGraphLimits.GraphParam` is a real parameter of finite simple graphs, with
  `TauCeti.DenseGraphLimits.IsIsoInvariant` imposing agreement along isomorphisms;
* `TauCeti.DenseGraphLimits.connectionMatrix` is an indexed block of the connection matrix
  `M(f, k)`;
* `TauCeti.DenseGraphLimits.IsReflectionPositive`,
  `TauCeti.DenseGraphLimits.IsMultiplicative` and
  `TauCeti.DenseGraphLimits.IsNormalized` are the three remaining structural conditions.

## Main results

* `TauCeti.DenseGraphLimits.isHermitian_connectionMatrix` — isomorphism invariance makes connection
  matrices Hermitian because the two gluing orders are isomorphic;
* `TauCeti.DenseGraphLimits.IsReflectionPositive.posSemidef` reindexes the definition, which
  quantifies over `Fin n`-indexed families, to an arbitrary finite index type;
* `TauCeti.DenseGraphLimits.IsReflectionPositive.nonneg_glue_self` is the diagonal consequence
  `0 ≤ f` on a self-gluing;
* `TauCeti.DenseGraphLimits.IsMultiplicative.apply_sum_bot` says adjoining any finite edgeless
  graph does not change a multiplicative, normalized parameter.

The section `Examples` records that the four conditions are simultaneously satisfiable — the
parameter constantly `1`, which is the homomorphism density of the constant graphon `W ≡ 1` — and
that reflection positivity is not automatic.

## Implementation

`connectionMatrix` takes an arbitrary index type: the `Matrix ι ι ℝ` it produces needs no
finiteness, and `IsReflectionPositive` supplies `Fin n` where positive semidefiniteness is
asserted.  `IsReflectionPositive.posSemidef` then recovers the arbitrary finite index case, since
a connection matrix on `ι` is a submatrix of one on `Fin (Fintype.card ι)` along
`Fintype.equivFin`.

## References

* `TauCetiRoadmap/DenseGraphLimits/Suggested.lean` — source for the formal signatures.
* L. Lovász, B. Szegedy, *Limits of dense graph sequences*, JCTB 96 (2006), 933–957, Theorem 2.2 —
  the four structural conditions and the representability theorem they characterise.
* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), Chapters 5
  and 6.
-/

public section

namespace TauCeti.DenseGraphLimits

/-- A **graph parameter**: a real-valued parameter of finite simple graphs, indexed over the
`Fin`-representatives.  Isomorphism invariance is imposed separately, as `IsIsoInvariant`. -/
abbrev GraphParam := (n : ℕ) → SimpleGraph (Fin n) → ℝ

/-- A graph parameter is **isomorphism invariant** when it agrees on isomorphic graphs.  This is
the standing hypothesis that makes `f` a genuine parameter of graphs rather than a
labelling-sensitive function on `Fin n`. -/
def IsIsoInvariant (f : GraphParam) : Prop :=
  ∀ (n₁ n₂ : ℕ) (F₁ : SimpleGraph (Fin n₁)) (F₂ : SimpleGraph (Fin n₂)),
    Nonempty (F₁ ≃g F₂) → f n₁ F₁ = f n₂ F₂

/-- The **connection matrix** of a graph parameter on a family `A : ι → LabeledGraph k` of
`k`-labeled graphs: the `ι × ι` matrix whose `(i, j)` entry is `f` on the unlabeled graph
underlying the gluing of `A i` and `A j`.  It is an indexed block of the full connection matrix
`M(f, k)`. -/
noncomputable def connectionMatrix (f : GraphParam) {k : ℕ} {ι : Type*} (A : ι → LabeledGraph k) :
    Matrix ι ι ℝ :=
  Matrix.of fun i j =>
    f ((A i).glue (A j)).forgetLabels.1 ((A i).glue (A j)).forgetLabels.2

/-- The connection-matrix entry law. -/
@[simp]
theorem connectionMatrix_apply (f : GraphParam) {k : ℕ} {ι : Type*} (A : ι → LabeledGraph k)
    (i j : ι) :
    connectionMatrix f A i j
      = f ((A i).glue (A j)).forgetLabels.1 ((A i).glue (A j)).forgetLabels.2 := by
  rw [connectionMatrix.eq_1]
  rfl

/-- Connection matrices of an isomorphism-invariant parameter are symmetric: gluing commutes up to
isomorphism. -/
theorem connectionMatrix_comm (f : GraphParam) (hf : IsIsoInvariant f) {k : ℕ} {ι : Type*}
    (A : ι → LabeledGraph k) (i j : ι) :
    connectionMatrix f A i j = connectionMatrix f A j i :=
  hf _ _ _ _ ⟨LabeledGraph.glueCommIso (A i) (A j)⟩

/-- Connection matrices of an isomorphism-invariant parameter are Hermitian because the two
gluing orders are isomorphic. -/
theorem isHermitian_connectionMatrix (f : GraphParam) (hf : IsIsoInvariant f) {k : ℕ} {ι : Type*}
    (A : ι → LabeledGraph k) : (connectionMatrix f A).IsHermitian := by
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.conjTranspose_apply, star_trivial]
  exact connectionMatrix_comm f hf A j i

/-- A graph parameter is **reflection positive** when every finite connection matrix is positive
semidefinite — every finite principal block of each `M(f, k)` is PSD.  The definition quantifies
over `Fin n`-indexed families; `IsReflectionPositive.posSemidef` recovers an arbitrary finite index
type. -/
def IsReflectionPositive (f : GraphParam) : Prop :=
  ∀ (k n : ℕ) (A : Fin n → LabeledGraph k), (connectionMatrix f A).PosSemidef

/-- A graph parameter is **multiplicative** when it turns disjoint unions into products, with the
disjoint union reindexed to `Fin (n₁ + n₂)` along `finSumFinEquiv` to stay on
`Fin`-representatives. -/
def IsMultiplicative (f : GraphParam) : Prop :=
  ∀ (n₁ n₂ : ℕ) (F₁ : SimpleGraph (Fin n₁)) (F₂ : SimpleGraph (Fin n₂)),
    f (n₁ + n₂) ((F₁ ⊕g F₂).map finSumFinEquiv.toEmbedding) = f n₁ F₁ * f n₂ F₂

/-- A graph parameter is **normalized** when its value on the one-vertex graph `K₁` is `1`. -/
def IsNormalized (f : GraphParam) : Prop := f 1 ⊥ = 1

/-- Reflection positivity for an arbitrary finite index type.  A connection matrix on `ι` is the
`Fintype.equivFin ι` submatrix of one on `Fin (Fintype.card ι)`, and positive semidefiniteness is
invariant under reindexing by an equivalence. -/
theorem IsReflectionPositive.posSemidef {f : GraphParam} (hf : IsReflectionPositive f) {k : ℕ}
    {ι : Type*} [Finite ι] (A : ι → LabeledGraph k) : (connectionMatrix f A).PosSemidef := by
  classical
  have _inst : Fintype ι := Fintype.ofFinite ι
  have hsub : connectionMatrix f (A ∘ (Fintype.equivFin ι).symm) =
      (connectionMatrix f A).submatrix (Fintype.equivFin ι).symm (Fintype.equivFin ι).symm := rfl
  have h := hf k (Fintype.card ι) (A ∘ (Fintype.equivFin ι).symm)
  rw [hsub] at h
  exact (Matrix.posSemidef_submatrix_equiv (Fintype.equivFin ι).symm).1 h

/-- The diagonal of a connection matrix is nonnegative: a reflection-positive parameter is
nonnegative on every self-gluing. -/
theorem IsReflectionPositive.nonneg_glue_self {f : GraphParam} (hf : IsReflectionPositive f)
    {k : ℕ} (G : LabeledGraph k) : 0 ≤ f (G.glue G).n (G.glue G).graph := by
  have h := (hf.posSemidef fun _ : Fin 1 => G).diag_nonneg (i := 0)
  simpa [connectionMatrix] using h

/-- A multiplicative, normalized parameter is `1` on every edgeless graph. -/
theorem IsMultiplicative.apply_bot {f : GraphParam} (hmul : IsMultiplicative f)
    (hnorm : IsNormalized f) (n : ℕ) : f n (⊥ : SimpleGraph (Fin n)) = 1 := by
  have map_sum_bot (a b : ℕ) :
      (((⊥ : SimpleGraph (Fin a)) ⊕g (⊥ : SimpleGraph (Fin b))).map
        finSumFinEquiv.toEmbedding) = ⊥ := by
    rw [eq_bot_iff, SimpleGraph.map_le_iff_le_comap]
    intro u v huv
    cases u <;> cases v <;> simp_all
  induction n with
  | zero =>
      have h := hmul 0 1 (⊥ : SimpleGraph (Fin 0)) (⊥ : SimpleGraph (Fin 1))
      rw [map_sum_bot, hnorm, mul_one] at h
      simpa using h.symm
  | succ n ih =>
      have h := hmul n 1 (⊥ : SimpleGraph (Fin n)) (⊥ : SimpleGraph (Fin 1))
      rw [map_sum_bot, ih, hnorm, mul_one] at h
      simpa using h

/-- A multiplicative, normalized parameter is unchanged by adjoining any finite edgeless graph. -/
theorem IsMultiplicative.apply_sum_bot {f : GraphParam} (hmul : IsMultiplicative f)
    (hnorm : IsNormalized f) (n m : ℕ) (F : SimpleGraph (Fin n)) :
    f (n + m) ((F ⊕g (⊥ : SimpleGraph (Fin m))).map finSumFinEquiv.toEmbedding) = f n F := by
  rw [hmul n m F ⊥, hmul.apply_bot hnorm m, mul_one]

section Examples

/-! ### Consistency and adversarial checks

The four structural conditions are simultaneously satisfiable.  Reflection positivity is not
implied by isomorphism invariance alone.  The parameter constantly `1` is the homomorphism density
`t(·, W)` of the constant graphon `W ≡ 1`. -/

/-- The constant parameter `1` is isomorphism invariant. -/
theorem isIsoInvariant_one : IsIsoInvariant fun _ _ => (1 : ℝ) := fun _ _ _ _ _ => rfl

/-- The constant parameter `1` is multiplicative. -/
theorem isMultiplicative_one : IsMultiplicative fun _ _ => (1 : ℝ) :=
  fun _ _ _ _ => (one_mul 1).symm

/-- The constant parameter `1` is normalized. -/
theorem isNormalized_one : IsNormalized fun _ _ => (1 : ℝ) := by
  rw [IsNormalized.eq_1]

/-- The constant parameter `1` is reflection positive: its connection matrices are the all-ones
matrices, the outer square of the all-ones vector. -/
theorem isReflectionPositive_one : IsReflectionPositive fun _ _ => (1 : ℝ) := by
  intro k n A
  have h : connectionMatrix (fun _ _ => (1 : ℝ)) A
      = Matrix.vecMulVec (1 : Fin n → ℝ) (star (1 : Fin n → ℝ)) := by
    ext i j
    simp [connectionMatrix, Matrix.vecMulVec_apply]
  rw [h]
  exact Matrix.posSemidef_vecMulVec_self_star _

/-- Isomorphism invariance alone does not imply reflection positivity: the constant parameter `-1`
is isomorphism invariant, yet it is negative on a self-gluing. -/
theorem not_isReflectionPositive_neg_one : ¬ IsReflectionPositive fun _ _ => (-1 : ℝ) := by
  intro h
  have := h.nonneg_glue_self (⟨1, ⊥, Fin.elim0, fun a => a.elim0⟩ : LabeledGraph 0)
  norm_num at this

end Examples

end TauCeti.DenseGraphLimits
