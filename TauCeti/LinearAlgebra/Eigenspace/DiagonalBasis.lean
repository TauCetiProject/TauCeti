/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import TauCeti.LinearAlgebra.Basis.Basic

/-!
# Invariant subspaces of an endomorphism diagonal in a basis

An endomorphism `f` of a module that is diagonal in a basis `b`, so `f (b i) = a i • b i`, scales
the `i`-th coordinate of every vector by the eigenvalue `a i`.  When the eigenvalues are pairwise
distinct, that is when `a` is injective, this pins down the invariant subspaces: an `f`-invariant
subspace contains every basis vector occurring in one of its elements, hence is spanned by the
basis vectors it contains, and a nonzero eigenvector of `f` is a multiple of a single basis
vector.  Neither is automatic for an operator with repeated eigenvalues.

The mechanism is that a coordinate of a vector `w` can be cleared without disturbing the others:
`f w - a j • w` again lies in any invariant subspace containing `w`, and its `k`-th coordinate is
`(a k - a j) * b.repr w k`, which vanishes at `k = j` and, by injectivity of `a`, at no other
index where `w` had a nonzero coordinate.  An induction on the number of nonzero coordinates then
strips a vector down to a single basis vector.

Mathlib records the neighbouring facts in eigenspace language: eigenspaces for distinct
eigenvalues are independent (`Module.End.eigenspaces_iSupIndep`), and eigenvectors for distinct
eigenvalues are linearly independent (`Module.End.eigenvectors_linearIndependent'`); neither says
what an invariant subspace looks like.  `TauCeti.iSup_inf_iInf_eigenspace_of_invariant` does cut
an invariant submodule out by eigenspaces, but for a commuting family over an algebraically
closed field, in finite dimension, and with semisimple restrictions.  A diagonalizing basis
carries all of that for free and in coordinates, which is the form used here: no finiteness, no
algebraic closedness, and the answer names the basis vectors involved.

## Main definitions

* `Module.Basis.diagEnd`: the endomorphism scaling each basis vector `b i` by `a i`.

## Main results

* `Module.Basis.repr_apply_of_apply_basis`: the coordinates of `f w` are those of `w` scaled by
  the eigenvalues.
* `Module.Basis.diagEnd_apply_self`, `Module.Basis.repr_diagEnd`, `Module.Basis.diagEnd_one`,
  `Module.Basis.diagEnd_comp`, `Module.Basis.diagEnd_neg`,
  `Module.Basis.diagEnd_comp_apply_of_eigenvector`, and
  `Module.Basis.diagEnd_comp_eq_comp_diagEnd`: evaluation, coordinates, identity, composition,
  negation, eigenvector action, and intertwining of diagonal endomorphisms in a basis.
* `Module.Basis.apply_eq_smul_of_apply_basis`: if `f` and `g` are both diagonal in `b`, any
  `μ`-eigenvector of `f` is a `ν`-eigenvector of `g` whenever every basis index with
  `f`-eigenvalue `μ` has `g`-eigenvalue `ν`.
* `Module.Basis.repr_eq_zero_of_weight_ne`: a joint eigenvector has zero coordinate at a basis
  vector of a different joint weight.
* `Module.Basis.self_mem_of_repr_ne_zero`, `Module.Basis.eq_span_self_mem`,
  `Module.Basis.self_mem_of_repr_ne_zero_of_forall`, and
  `Module.Basis.eq_span_self_mem_of_forall`: an invariant subspace (for a single diagonal
  endomorphism with distinct eigenvalues, or for a jointly diagonal family whose joint weights are
  pairwise distinct) contains every basis vector occurring in one of its elements, and is spanned
  by the basis vectors it contains.
* `Module.Basis.exists_apply_eq_and_mem_span_singleton`: a nonzero eigenvector of `f` is a
  multiple of a single basis vector, whose eigenvalue is its eigenvalue.
* `Module.Basis.eigenspace_eq_span_image` and `Module.Basis.finrank_eigenspace_eq_card`: with
  repeated eigenvalues allowed, the `μ`-eigenspace is spanned by the basis vectors of eigenvalue
  `μ`, and its dimension is their number.
-/

public section

namespace TauCeti

variable {ι K V : Type*}

/-! ### The coordinates are scaled by the eigenvalues -/

section CommSemiring

variable [CommSemiring K] [AddCommMonoid V] [Module K V] {f : V →ₗ[K] V} {a : ι → K}

/-- **An endomorphism diagonal in a basis scales the coordinates**: if `f (b i) = a i • b i` for
every `i`, then `f` multiplies the `i`-th coordinate of every vector by `a i`. -/
theorem _root_.Module.Basis.repr_apply_of_apply_basis (b : Module.Basis ι K V)
    (hf : ∀ i, f (b i) = a i • b i) (w : V) (i : ι) :
    b.repr (f w) i = a i * b.repr w i := by
  have key : (Finsupp.lapply i).comp ((b.repr : V →ₗ[K] ι →₀ K).comp f)
      = (a i • Finsupp.lapply i).comp (b.repr : V →ₗ[K] ι →₀ K) := by
    refine b.ext fun j => ?_
    rcases eq_or_ne j i with rfl | hj
    · simp [hf j]
    · simp [hf j, hj]
  simpa using LinearMap.congr_fun key w

/-- The diagonal endomorphism in the basis `b` scaling each `b i` by `a i`. -/
noncomputable def _root_.Module.Basis.diagEnd (b : Module.Basis ι K V) (a : ι → K) :
    Module.End K V :=
  b.constr K fun i => a i • b i

/-- Evaluating `b.diagEnd a` on a basis vector scales it by `a i`. -/
@[simp]
theorem _root_.Module.Basis.diagEnd_apply_self (b : Module.Basis ι K V) (a : ι → K) (i : ι) :
    b.diagEnd a (b i) = a i • b i :=
  b.constr_basis K _ i

/-- `b.diagEnd a` scales the `i`-th basis coordinate of every vector by `a i`. -/
theorem _root_.Module.Basis.repr_diagEnd (b : Module.Basis ι K V) (a : ι → K) (w : V) (i : ι) :
    b.repr (b.diagEnd a w) i = a i * b.repr w i :=
  b.repr_apply_of_apply_basis (b.diagEnd_apply_self a) w i

/-- The diagonal endomorphism with all entries `1` is the identity. -/
@[simp]
theorem _root_.Module.Basis.diagEnd_one (b : Module.Basis ι K V) :
    b.diagEnd 1 = LinearMap.id :=
  b.ext fun i => by simp

/-- Composing two diagonal endomorphisms in the same basis multiplies their diagonal entries. -/
theorem _root_.Module.Basis.diagEnd_comp (b : Module.Basis ι K V) (a c : ι → K) :
    (b.diagEnd a).comp (b.diagEnd c) = b.diagEnd (fun i => a i * c i) :=
  b.ext fun i => by simp [smul_smul, mul_comm]

end CommSemiring

section CommRing

variable [CommRing K] [AddCommGroup V] [Module K V]

/-- Negating the diagonal entries negates the diagonal endomorphism. -/
@[simp]
theorem _root_.Module.Basis.diagEnd_neg (b : Module.Basis ι K V) (a : ι → K) :
    b.diagEnd (fun i => -a i) = -b.diagEnd a :=
  b.ext fun i => by simp [neg_smul]

end CommRing

section IsCancelMulZero

variable {κ : Type*} [CommSemiring K] [IsCancelMulZero K] [AddCommMonoid V] [Module K V]
  {f : κ → Module.End K V} {a : ι → κ → K}

/-- A joint eigenvector has zero coordinate at every basis vector of a different joint weight,
when a family of endomorphisms is diagonal in the basis. -/
theorem _root_.Module.Basis.repr_eq_zero_of_weight_ne (b : Module.Basis ι K V)
    (hf : ∀ i j, f j (b i) = a i j • b i) {w : V} {c : κ → K}
    (hw : ∀ j, f j w = c j • w) {i : ι} (hi : a i ≠ c) : b.repr w i = 0 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hi
  have hcoord := b.repr_apply_of_apply_basis (f := f j) (a := fun k => a k j)
    (fun k => hf k j) w i
  rw [hw j, map_smul, Finsupp.smul_apply, smul_eq_mul] at hcoord
  by_contra hne
  exact hj (mul_right_cancel₀ hne hcoord).symm

/-- If `f` and `g` are diagonal in the basis `b` with eigenvalues `a` and `c`, then any
`μ`-eigenvector of `f` is a `ν`-eigenvector of `g` provided `c i = ν` whenever `a i = μ`. -/
theorem _root_.Module.Basis.apply_eq_smul_of_apply_basis (b : Module.Basis ι K V)
    {f g : V →ₗ[K] V} {a c : ι → K}
    (hf : ∀ i, f (b i) = a i • b i) (hg : ∀ i, g (b i) = c i • b i)
    {w : V} {μ ν : K} (hw : f w = μ • w) (h : ∀ i, a i = μ → c i = ν) :
    g w = ν • w := by
  apply b.repr.injective
  ext i
  rw [b.repr_apply_of_apply_basis hg, map_smul, Finsupp.smul_apply, smul_eq_mul]
  by_cases hai : a i = μ
  · rw [h i hai]
  · have h0 : b.repr w i = 0 := b.repr_eq_zero_of_weight_ne (κ := Unit) (f := fun _ => f)
      (a := fun k _ => a k) (fun k _ => hf k) (fun _ => hw) (c := fun _ => μ)
      (fun hfn => hai (congr_fun hfn ()))
    simp [h0]

/-- A diagonal operator `b.diagEnd (fun i => g (a i))` acts by `g μ` on any `μ`-eigenvector
of an endomorphism `f` diagonal in `b` with eigenvalues `a`. -/
theorem _root_.Module.Basis.diagEnd_comp_apply_of_eigenvector (b : Module.Basis ι K V)
    {f : Module.End K V} {a : ι → K} (hf : ∀ i, f (b i) = a i • b i)
    (g : K → K) {w : V} {μ : K} (hw : f w = μ • w) :
    b.diagEnd (fun i => g (a i)) w = g μ • w :=
  b.apply_eq_smul_of_apply_basis hf (b.diagEnd_apply_self _) hw fun _ hi => congrArg g hi

/-- If `f` is diagonal in `b` with eigenvalues `a` and `φ` sends each `b i` to a
`ψ (a i)`-eigenvector of `f`, then `b.diagEnd (g₁ ∘ a)` intertwined across `φ` equals
`b.diagEnd (g₂ ∘ a)` whenever `g₁ (ψ (a i)) = g₂ (a i)` for all `i`. -/
theorem _root_.Module.Basis.diagEnd_comp_eq_comp_diagEnd (b : Module.Basis ι K V)
    {f φ : Module.End K V} {a : ι → K} (hf : ∀ i, f (b i) = a i • b i)
    (ψ g₁ g₂ : K → K) (hφ : ∀ i, f (φ (b i)) = ψ (a i) • φ (b i))
    (hg : ∀ i, g₁ (ψ (a i)) = g₂ (a i)) :
    (b.diagEnd (fun i => g₁ (a i))).comp φ = φ.comp (b.diagEnd (fun i => g₂ (a i))) := by
  refine b.ext fun i => ?_
  simp only [LinearMap.comp_apply]
  rw [b.diagEnd_comp_apply_of_eigenvector hf g₁ (hφ i), hg i, b.diagEnd_apply_self, map_smul]

end IsCancelMulZero

/-! ### Invariant subspaces are spanned by basis vectors -/

section CoordinateSubtraction

variable [CommRing K] [AddCommGroup V] [Module K V] {f : V →ₗ[K] V} {a : ι → K}

/-- **Clearing a coordinate**: subtracting from `f w` the multiple `a j • w` kills the `j`-th
coordinate and multiplies the `k`-th one by `a k - a j`. -/
private theorem repr_sub_smul_apply (b : Module.Basis ι K V) (hf : ∀ i, f (b i) = a i • b i)
    (w : V) (j k : ι) :
    b.repr (f w - a j • w) k = (a k - a j) * b.repr w k := by
  rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply,
    b.repr_apply_of_apply_basis hf, smul_eq_mul, sub_mul]

/-- The cleared vector has strictly smaller support: it loses the `j`-th coordinate and gains
none. -/
private theorem support_repr_sub_smul_subset [DecidableEq ι] (b : Module.Basis ι K V)
    (hf : ∀ i, f (b i) = a i • b i) (w : V) (j : ι) :
    (b.repr (f w - a j • w)).support ⊆ (b.repr w).support.erase j := by
  intro k hk
  have hk0 : b.repr (f w - a j • w) k ≠ 0 := Finsupp.mem_support_iff.1 hk
  rw [repr_sub_smul_apply b hf w j k] at hk0
  refine Finset.mem_erase.2 ⟨?_, Finsupp.mem_support_iff.2 (right_ne_zero_of_mul hk0)⟩
  rintro rfl
  exact hk0 (by rw [sub_self, zero_mul])

end CoordinateSubtraction

section Family

variable {κ : Type*} [Field K] [AddCommGroup V] [Module K V] {f : κ → V →ₗ[K] V}
  {a : ι → κ → K} {W : Submodule K V}

private theorem self_mem_aux (b : Module.Basis ι K V) (hf : ∀ i j, f j (b i) = a i j • b i)
    (ha : Function.Injective a) (hW : ∀ j, ∀ v ∈ W, f j v ∈ W) :
    ∀ (n : ℕ) (w : V), w ∈ W → (b.repr w).support.card ≤ n →
      ∀ i : ι, b.repr w i ≠ 0 → b i ∈ W := by
  classical
  intro n
  induction n with
  | zero =>
    intro w _ hcard i hi
    have hsupp : (b.repr w).support = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hcard)
    exact absurd (Finsupp.notMem_support_iff.1 (by rw [hsupp]; exact Finset.notMem_empty i)) hi
  | succ n ih =>
    intro w hw hcard i hi
    by_cases hsub : (b.repr w).support ⊆ {i}
    · -- the `i`-th coordinate is the only nonzero one, so `b i` is a multiple of `w`;
      -- naming that coordinate keeps it from being rewritten along with `w` below
      set c := b.repr w i
      have hmem : c⁻¹ • w ∈ W := W.smul_mem _ hw
      rwa [b.eq_smul_of_repr_support_subset_singleton hsub, smul_smul, inv_mul_cancel₀ hi,
        one_smul] at hmem
    · -- otherwise some other coordinate `j` is nonzero, and can be cleared using an index `t`
      -- at which the joint weights `a j` and `a i` differ
      obtain ⟨j, hjs, hji⟩ := Finset.not_subset.1 hsub
      have hjne : j ≠ i := fun h => hji (Finset.mem_singleton.2 h)
      obtain ⟨t, ht⟩ := Function.ne_iff.1 (ha.ne hjne)
      have hmem : f t w - a j t • w ∈ W := W.sub_mem (hW t w hw) (W.smul_mem _ hw)
      have hcard' : (b.repr (f t w - a j t • w)).support.card ≤ n := by
        have hle := Finset.card_le_card (support_repr_sub_smul_subset b (fun k => hf k t) w j)
        rw [Finset.card_erase_of_mem hjs] at hle
        have hpos : 0 < (b.repr w).support.card := Finset.card_pos.2 ⟨j, hjs⟩
        omega
      refine ih _ hmem hcard' i ?_
      rw [repr_sub_smul_apply b (fun k => hf k t) w j i]
      exact mul_ne_zero (sub_ne_zero.2 ht.symm) hi

/-- **An invariant subspace for a jointly diagonal family contains every basis vector occurring in
one of its elements**, when the joint weights `a : ι → κ → K` are pairwise distinct: any two
distinct basis indices are separated by at least one operator in the family, so extra coordinates
can be cleared one at a time. -/
theorem _root_.Module.Basis.self_mem_of_repr_ne_zero_of_forall (b : Module.Basis ι K V)
    (hf : ∀ i j, f j (b i) = a i j • b i) (ha : Function.Injective a)
    (hW : ∀ j, ∀ v ∈ W, f j v ∈ W) {w : V} (hw : w ∈ W) {i : ι} (hi : b.repr w i ≠ 0) :
    b i ∈ W :=
  self_mem_aux b hf ha hW _ w hw le_rfl i hi

/-- **An invariant subspace for a jointly diagonal family is spanned by the basis vectors it
contains**, when the joint weights `a : ι → κ → K` are pairwise distinct. -/
theorem _root_.Module.Basis.eq_span_self_mem_of_forall (b : Module.Basis ι K V)
    (hf : ∀ i j, f j (b i) = a i j • b i) (ha : Function.Injective a)
    (hW : ∀ j, ∀ v ∈ W, f j v ∈ W) :
    W = Submodule.span K {v | ∃ i : ι, b i = v ∧ v ∈ W} := by
  refine le_antisymm (fun w hw => ?_) (Submodule.span_le.2 ?_)
  · rw [← b.linearCombination_repr w, Finsupp.linearCombination_apply, Finsupp.sum]
    refine Submodule.sum_mem _ fun k hk => ?_
    exact Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨k, rfl, b.self_mem_of_repr_ne_zero_of_forall hf ha hW hw (Finsupp.mem_support_iff.1 hk)⟩)
  · rintro v ⟨-, -, hv⟩
    exact hv

end Family

section Field

variable [Field K] [AddCommGroup V] [Module K V] {f : V →ₗ[K] V} {a : ι → K}
  {W : Submodule K V}

/-- **An invariant subspace contains every basis vector occurring in one of its elements**, when
the endomorphism is diagonal in the basis with pairwise distinct eigenvalues: the coordinates of
an element can then be separated by repeatedly clearing one of them. -/
theorem _root_.Module.Basis.self_mem_of_repr_ne_zero (b : Module.Basis ι K V)
    (hf : ∀ i, f (b i) = a i • b i) (ha : Function.Injective a) (hW : ∀ v ∈ W, f v ∈ W) {w : V}
    (hw : w ∈ W) {i : ι} (hi : b.repr w i ≠ 0) : b i ∈ W :=
  b.self_mem_of_repr_ne_zero_of_forall (κ := Unit) (f := fun _ => f) (a := fun i _ => a i)
    (fun i _ => hf i) (fun _ _ h => ha (congr_fun h ())) (fun _ => hW) hw hi

/-- **An invariant subspace is spanned by the basis vectors it contains**, when the endomorphism
is diagonal in the basis with pairwise distinct eigenvalues. -/
theorem _root_.Module.Basis.eq_span_self_mem (b : Module.Basis ι K V)
    (hf : ∀ i, f (b i) = a i • b i) (ha : Function.Injective a) (hW : ∀ v ∈ W, f v ∈ W) :
    W = Submodule.span K {v | ∃ i : ι, b i = v ∧ v ∈ W} :=
  b.eq_span_self_mem_of_forall (κ := Unit) (f := fun _ => f) (a := fun i _ => a i)
    (fun i _ => hf i) (fun _ _ h => ha (congr_fun h ())) (fun _ => hW)

end Field

/-! ### Eigenvectors are multiples of basis vectors -/

section CancelMulZero

variable [CommSemiring K] [IsCancelMulZero K] [AddCommMonoid V] [Module K V] {f : V →ₗ[K] V}
  {a : ι → K}

/-- **A nonzero eigenvector is a multiple of a single basis vector**, when the endomorphism is
diagonal in the basis with pairwise distinct eigenvalues, and its eigenvalue is the eigenvalue of
that basis vector. -/
theorem _root_.Module.Basis.exists_apply_eq_and_mem_span_singleton (b : Module.Basis ι K V)
    (hf : ∀ i, f (b i) = a i • b i) (ha : Function.Injective a) {w : V} (hw : w ≠ 0) {c : K}
    (hfw : f w = c • w) : ∃ i : ι, a i = c ∧ w ∈ Submodule.span K {b i} := by
  classical
  have hcoord : ∀ k : ι, a k * b.repr w k = c * b.repr w k := by
    intro k
    rw [← b.repr_apply_of_apply_basis hf, hfw, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have hrne : b.repr w ≠ 0 := fun h => hw (b.repr.map_eq_zero_iff.1 h)
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hrne
  rw [Finsupp.coe_zero, Pi.zero_apply] at hi
  have hci : a i = c := mul_right_cancel₀ hi (hcoord i)
  refine ⟨i, hci, ?_⟩
  have hsupp : (b.repr w).support ⊆ {i} := fun k hk =>
    Finset.mem_singleton.2
      (ha ((mul_right_cancel₀ (Finsupp.mem_support_iff.1 hk) (hcoord k)).trans hci.symm))
  rw [b.eq_smul_of_repr_support_subset_singleton hsupp]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

end CancelMulZero

/-! ### Eigenspaces are coordinate subspaces -/

section Eigenspace

variable [CommRing K] [IsCancelMulZero K] [AddCommGroup V] [Module K V] {f : Module.End K V}
  {a : ι → K}

/-- **The eigenspaces of an endomorphism diagonal in a basis are coordinate subspaces**: the
`μ`-eigenspace is spanned by the basis vectors of eigenvalue `μ`. The eigenvalues need not be
pairwise distinct. -/
theorem _root_.Module.Basis.eigenspace_eq_span_image (b : Module.Basis ι K V)
    (hf : ∀ i, f (b i) = a i • b i) (μ : K) :
    f.eigenspace μ = Submodule.span K (b '' {i | a i = μ}) := by
  refine le_antisymm (fun w hw => b.mem_span_image.mpr fun i hi => ?_) (Submodule.span_le.mpr ?_)
  · have h := b.repr_apply_of_apply_basis hf w i
    rw [Module.End.mem_eigenspace_iff.mp hw, map_smul, Finsupp.smul_apply, smul_eq_mul] at h
    exact (mul_right_cancel₀ (Finsupp.mem_support_iff.mp hi) h).symm
  · rintro _ ⟨i, hi, rfl⟩
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, hf i, Set.mem_ofPred_eq.mp hi]

/-- **The eigenspace dimensions of an endomorphism diagonal in a basis count basis vectors**: the
`μ`-eigenspace has dimension the number of basis vectors of eigenvalue `μ`. Only that fibre has
to be finite. -/
theorem _root_.Module.Basis.finrank_eigenspace_eq_card [Nontrivial K] (b : Module.Basis ι K V)
    (hf : ∀ i, f (b i) = a i • b i) (μ : K) [Finite {i // a i = μ}] :
    Module.finrank K (f.eigenspace μ) = Nat.card {i // a i = μ} := by
  have := Fintype.ofFinite {i // a i = μ}
  rw [b.eigenspace_eq_span_image hf μ, ← Subtype.range_coe_subtype, ← Set.range_comp,
    finrank_span_eq_card (b.linearIndependent.comp _ Subtype.val_injective),
    Nat.card_eq_fintype_card]

end Eigenspace

end TauCeti
