/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.LinearAlgebra.BilinearForm.LinearIndependent
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Symplectic bases of nondegenerate alternating forms

A nondegenerate alternating bilinear form `B` on a finite-dimensional vector space `V` over a
field has a **symplectic basis**: a basis `b` indexed by `Fin m ⊕ Fin m` in which the matrix of
`B` is the standard matrix `Matrix.J (Fin m) K`, so `B (b (inr a)) (b (inl a)) = 1`, every other
pair of basis vectors is orthogonal, and in particular `V` has even dimension `2 * m`.

The theorem is proved in a graded form. Suppose `V` is spanned by a family of subspaces
`W : ι → Submodule K V`, the index type carries an involution `σ`, and `B` pairs `W i` with `W j`
trivially unless `j = σ i`. Then the symplectic basis can be chosen to consist of vectors each
lying in some `W i`. The ungraded theorem is the case of a single subspace `⊤`. The graded form
is what a diagonalizable subgroup of a symplectic group needs: its weight spaces are paired by
inversion of characters, and a homogeneous symplectic basis is a symplectic change of coordinates
diagonalizing the subgroup.

The proof is the classical induction on dimension. A nonzero homogeneous vector `e ∈ W i` pairs
nontrivially with some homogeneous `f ∈ W (σ i)`, normalized to `B f e = 1`. The orthogonal
complement of `span {e, f}` has dimension two less, carries a nondegenerate restriction of `B`,
and is spanned by its intersections with the `W j`, because the projection
`u ↦ u - B f u • e + B e u • f` onto it preserves homogeneity. Adjoining `e` and `f` to a
homogeneous symplectic basis of the complement gives one of `V`. The facts about a single
hyperbolic pair `e, f` hold over any commutative ring and are stated at that level.

## Main declarations

* `LinearMap.BilinForm.IsAlt.restrict_nondegenerate_orthogonal_span_pair`: a nondegenerate
  alternating form stays nondegenerate on the orthogonal complement of a hyperbolic pair.
* `LinearMap.BilinForm.IsAlt.exists_basis_apply_eq_J_of_basis_orthogonal_span_pair`: adjoining a
  hyperbolic pair to a symplectic basis of the orthogonal complement of its span gives a
  symplectic basis.
* `LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J_of_iSup_eq_top`: **a nondegenerate
  alternating form on a compatibly graded space has a homogeneous symplectic basis.**
* `LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J`: **a nondegenerate alternating form has
  a symplectic basis.**
* `LinearMap.BilinForm.IsAlt.even_finrank`: a space carrying a nondegenerate alternating form has
  even dimension.

## References

* E. Artin, *Geometric Algebra* (1957), Theorem 3.7.
* S. Lang, *Algebra*, revised 3rd ed. (2002), Chapter XV, Theorem 8.1.
-/

public section

namespace LinearMap.BilinForm

open LinearMap (BilinForm)
open Module Submodule

section CommSemiring

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- In a space spanned by a family of subspaces paired trivially by `B` except along an
involution `σ`, a nonzero vector of `W i` pairs nontrivially with some vector of `W (σ i)`. -/
theorem Nondegenerate.exists_mem_apply_ne_zero_of_iSup_eq_top {B : BilinForm R M}
    (hnd : B.Nondegenerate)
    {ι : Type*} {W : ι → Submodule R M} {σ : ι → ι} (hσ : Function.Involutive σ)
    (hW : ⨆ i, W i = ⊤) (horth : ∀ i j, j ≠ σ i → ∀ v ∈ W i, ∀ w ∈ W j, B v w = 0)
    {i : ι} {v : M} (hv : v ∈ W i) (hv0 : v ≠ 0) : ∃ w ∈ W (σ i), B w v ≠ 0 := by
  by_contra! hcon
  refine hv0 (hnd.2 v fun u => ?_)
  have hu : u ∈ ⨆ i, W i := hW ▸ mem_top
  refine iSup_induction (motive := fun u => B u v = 0) W hu (fun j u hu => ?_) (by simp)
    (fun x y hx hy => by simp [hx, hy])
  by_cases hj : j = σ i
  · exact hcon u (hj ▸ hu)
  · exact horth j i (fun hi => hj (by rw [hi, hσ])) u hu v hv

end CommSemiring

section CommRing

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

variable {B : BilinForm R M} (hB : B.IsAlt) {e f : M} (hfe : B f e = 1)
include hB hfe

/-- Two vectors pairing to `1` under an alternating form are linearly independent. -/
theorem IsAlt.linearIndependent_pair_of_apply_eq_one : LinearIndependent R ![e, f] := by
  have hef : B e f = -1 := by rw [← hB.neg_eq, hfe]
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1 := congrArg (B f) hst
  have h2 := congrArg (B e) hst
  simp only [map_add, map_smul, hfe, hef, hB.self_eq_zero, smul_eq_mul, mul_one, mul_zero,
    add_zero, zero_add, mul_neg, map_zero, neg_eq_zero] at h1 h2
  exact ⟨h1, h2⟩

/-- The projection `u ↦ u - B f u • e + B e u • f` lands in the orthogonal complement of the span
of the hyperbolic pair `e, f`. -/
theorem IsAlt.sub_smul_add_smul_mem_orthogonal_span_pair (u : M) :
    u - B f u • e + B e u • f ∈ B.orthogonal (span R {e, f}) := by
  have hef : B e f = -1 := by rw [← hB.neg_eq, hfe]
  rw [mem_orthogonal_span_pair_iff]
  simp [hfe, hef, hB.self_eq_zero]

/-- The restriction of a nondegenerate alternating form to the orthogonal complement of the span
of a hyperbolic pair is nondegenerate. -/
theorem IsAlt.restrict_nondegenerate_orthogonal_span_pair (hnd : B.Nondegenerate) :
    (B.restrict (B.orthogonal (span R {e, f}))).Nondegenerate := by
  have hrefl : (B.restrict (B.orthogonal (span R {e, f}))).IsRefl := fun x y h => by
    rw [restrict_apply] at h ⊢
    exact hB.isRefl x y h
  refine (IsRefl.nondegenerate_iff_separatingLeft hrefl).2 fun z hz => ?_
  obtain ⟨hez, hfz⟩ := (mem_orthogonal_span_pair_iff B).1 z.2
  suffices key : (z : M) = 0 from Submodule.coe_eq_zero.1 key
  refine hnd.1 z fun u => ?_
  have hz' := hz ⟨_, hB.sub_smul_add_smul_mem_orthogonal_span_pair hfe u⟩
  simpa [← hB.neg_eq e z, ← hB.neg_eq f z, hez, hfz] using hz'

/-- If `e ∈ W i` and `f ∈ W (σ i)` form a hyperbolic pair, the orthogonal complement of their
span is spanned by its intersections with the `W j`. -/
private theorem IsAlt.iSup_comap_orthogonal_span_pair_eq_top {ι : Type*} {W : ι → Submodule R M}
    {σ : ι → ι} (hσ : Function.Involutive σ) (hW : ⨆ i, W i = ⊤)
    (horth : ∀ i j, j ≠ σ i → ∀ v ∈ W i, ∀ w ∈ W j, B v w = 0)
    {i : ι} (he : e ∈ W i) (hf : f ∈ W (σ i)) :
    ⨆ j, (W j).comap (B.orthogonal (span R {e, f})).subtype = ⊤ := by
  set Z := B.orthogonal (span R {e, f}) with hZ
  set p : M →ₗ[R] M := LinearMap.id - (B f).smulRight e + (B e).smulRight f with hp_def
  have hpu : ∀ u, p u = u - B f u • e + B e u • f := fun u => by simp [hp_def]
  have hpZ : ∀ u, p u ∈ Z := fun u => by
    rw [hpu]
    exact hB.sub_smul_add_smul_mem_orthogonal_span_pair hfe u
  -- The projection of a homogeneous vector is homogeneous of the same degree, so the projection
  -- of every vector lies in the span of the graded pieces of `Z`.
  have hp : ∀ u, (⟨p u, hpZ u⟩ : Z) ∈ ⨆ j, (W j).comap Z.subtype := by
    intro u
    have hu : u ∈ ⨆ i, W i := hW ▸ mem_top
    refine iSup_induction (motive := fun u => (⟨p u, hpZ u⟩ : Z) ∈ ⨆ j, (W j).comap Z.subtype)
      W hu (fun j u hu => mem_iSup_of_mem j ?_) ?_ (fun x y hx hy => ?_)
    · have h1 : B f u • e ∈ W j := by
        by_cases hj : j = i
        · exact hj ▸ smul_mem _ _ he
        · rw [horth (σ i) j (fun h => hj (by rw [h, hσ])) f hf u hu, zero_smul]
          exact zero_mem _
      have h2 : B e u • f ∈ W j := by
        by_cases hj : j = σ i
        · exact hj ▸ smul_mem _ _ hf
        · rw [horth i j hj e he u hu, zero_smul]
          exact zero_mem _
      simpa [hpu] using add_mem (sub_mem hu h1) h2
    · have h0 : (⟨p 0, hpZ 0⟩ : Z) = 0 := Subtype.ext (map_zero p)
      rw [h0]
      exact zero_mem _
    · have hxy : (⟨p (x + y), hpZ _⟩ : Z) = ⟨p x, hpZ x⟩ + ⟨p y, hpZ y⟩ :=
        Subtype.ext (map_add p x y)
      rw [hxy]
      exact add_mem hx hy
  -- The projection fixes `Z` pointwise.
  refine eq_top_iff.2 fun z _ => ?_
  obtain ⟨hez, hfz⟩ := (mem_orthogonal_span_pair_iff B).1 z.2
  have hz : (⟨p z, hpZ z⟩ : Z) = z := Subtype.ext (by simp [hpu, hez, hfz])
  exact hz ▸ hp z

/-- The Gram matrix of the family obtained by adjoining a hyperbolic pair `e, f` to a symplectic
family `c` orthogonal to both is again the standard symplectic matrix. -/
private theorem IsAlt.apply_cons_cons_eq_J {m : ℕ}
    {c : Fin m ⊕ Fin m → M} (hc : ∀ x y, B (c x) (c y) = Matrix.J (Fin m) R x y)
    (hec : ∀ x, B e (c x) = 0) (hfc : ∀ x, B f (c x) = 0) (x y : Fin (m + 1) ⊕ Fin (m + 1)) :
    B (Sum.elim (Fin.cons e fun a => c (Sum.inl a)) (Fin.cons f fun a => c (Sum.inr a)) x)
        (Sum.elim (Fin.cons e fun a => c (Sum.inl a)) (Fin.cons f fun a => c (Sum.inr a)) y) =
      Matrix.J (Fin (m + 1)) R x y := by
  have hef : B e f = -1 := by rw [← hB.neg_eq, hfe]
  have hce : ∀ x, B (c x) e = 0 := fun x => by rw [← hB.neg_eq, hec, neg_zero]
  have hcf : ∀ x, B (c x) f = 0 := fun x => by rw [← hB.neg_eq, hfc, neg_zero]
  rcases x with x | x <;> rcases y with y | y <;>
    induction x using Fin.cases <;> induction y using Fin.cases <;>
    simp [Matrix.J, Matrix.fromBlocks, hfe, hef, hB.self_eq_zero, hc, hec, hfc, hce, hcf,
      Matrix.one_apply, Fin.succ_inj, Fin.succ_ne_zero, fun a : Fin m => (Fin.succ_ne_zero a).symm]

end CommRing

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {B : BilinForm K V} (hB : B.IsAlt) (hnd : B.Nondegenerate)
include hB hnd

section HyperbolicPair

variable {e f : V} (hfe : B f e = 1)
include hfe

/-- The orthogonal complement of the span of a hyperbolic pair has codimension two. -/
theorem IsAlt.finrank_orthogonal_span_pair_add_two :
    finrank K (B.orthogonal (span K {e, f})) + 2 = finrank K V := by
  have h := finrank_add_finrank_orthogonal hB.isRefl (span K {e, f})
  rw [orthogonal_top_eq_bot hnd, inf_bot_eq, finrank_bot, add_zero] at h
  have hU : finrank K (span K {e, f}) = 2 := by
    rw [← Matrix.range_cons_cons_empty e f ![], finrank_span_eq_card
      (hB.linearIndependent_pair_of_apply_eq_one hfe), Fintype.card_fin]
  omega

/-- **Adjoining a hyperbolic pair to a symplectic basis of the orthogonal complement of its span
gives a symplectic basis.** The new basis puts `e` and `f` in the positions `inl 0` and `inr 0`
and shifts the given basis of the complement to the successor positions. -/
theorem IsAlt.exists_basis_apply_eq_J_of_basis_orthogonal_span_pair {m : ℕ}
    (c : Basis (Fin m ⊕ Fin m) K (B.orthogonal (span K {e, f})))
    (hc : ∀ x y, B (c x) (c y) = Matrix.J (Fin m) K x y) :
    ∃ b : Basis (Fin (m + 1) ⊕ Fin (m + 1)) K V,
      (∀ x y, B (b x) (b y) = Matrix.J (Fin (m + 1)) K x y) ∧
        ⇑b = Sum.elim (Fin.cons e fun a => c (Sum.inl a)) (Fin.cons f fun a => c (Sum.inr a)) := by
  have hec : ∀ x, B e (c x) = 0 := fun x => ((mem_orthogonal_span_pair_iff B).1 (c x).2).1
  have hfc : ∀ x, B f (c x) = 0 := fun x => ((mem_orthogonal_span_pair_iff B).1 (c x).2).2
  let d : Fin (m + 1) ⊕ Fin (m + 1) → V :=
    Sum.elim (Fin.cons e fun a => c (Sum.inl a)) (Fin.cons f fun a => c (Sum.inr a))
  have hd : ∀ x y, B (d x) (d y) = Matrix.J (Fin (m + 1)) K x y :=
    hB.apply_cons_cons_eq_J hfe hc hec hfc
  have hG : (Matrix.of fun x y => B (d x) (d y)) = Matrix.J (Fin (m + 1)) K := Matrix.ext hd
  have hli : LinearIndependent K d := by
    refine B.linearIndependent_of_det_ne_zero ?_
    rw [hG]
    exact (Matrix.isUnit_det_J _ _).ne_zero
  have hcard : Fintype.card (Fin (m + 1) ⊕ Fin (m + 1)) = finrank K V := by
    rw [← hB.finrank_orthogonal_span_pair_add_two hnd hfe, finrank_eq_card_basis c]
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  exact ⟨basisOfLinearIndependentOfCardEqFinrank hli hcard,
    by simpa [coe_basisOfLinearIndependentOfCardEqFinrank] using hd,
    coe_basisOfLinearIndependentOfCardEqFinrank hli hcard⟩

end HyperbolicPair

omit [AddCommGroup V] [Module K V] [FiniteDimensional K V] hB hnd in
/-- The induction behind `IsAlt.exists_basis_toMatrix_eq_J_of_iSup_eq_top`, stated for every
space of a given dimension. -/
private theorem exists_basis_apply_eq_J_of_iSup_eq_top_aux (n : ℕ) :
    ∀ (V : Type*) [AddCommGroup V] [Module K V] [FiniteDimensional K V],
      finrank K V = n → ∀ (B : BilinForm K V), B.IsAlt → B.Nondegenerate →
      ∀ {ι : Type*} (W : ι → Submodule K V) (σ : ι → ι), Function.Involutive σ →
        ⨆ i, W i = ⊤ → (∀ i j, j ≠ σ i → ∀ v ∈ W i, ∀ w ∈ W j, B v w = 0) →
        ∃ (m : ℕ) (b : Basis (Fin m ⊕ Fin m) K V),
          (∀ x y, B (b x) (b y) = Matrix.J (Fin m) K x y) ∧ ∀ x, ∃ i, b x ∈ W i := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ hn B hB hnd ι W σ hσ hW horth
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact ⟨0, Basis.empty V, fun x => isEmptyElim x, fun x => isEmptyElim x⟩
  -- Choose a nonzero homogeneous vector `e` and a homogeneous partner `f` with `B f e = 1`.
  obtain ⟨i, hi⟩ : ∃ i, W i ≠ ⊥ := by
    by_contra! h
    exact bot_ne_top ((iSup_eq_bot.2 h).symm.trans hW)
  obtain ⟨e, he, he0⟩ := (Submodule.ne_bot_iff _).1 hi
  obtain ⟨w, hw, hwe⟩ := hnd.exists_mem_apply_ne_zero_of_iSup_eq_top hσ hW horth he he0
  set f := (B w e)⁻¹ • w with hf_def
  have hf : f ∈ W (σ i) := smul_mem _ _ hw
  have hfe : B f e = 1 := by rw [hf_def]; simp [inv_mul_cancel₀ hwe]
  -- Apply the induction hypothesis to the orthogonal complement of `span {e, f}`.
  set Z := B.orthogonal (span K {e, f}) with hZ
  have hZn : finrank K Z + 2 = n := hn ▸ hB.finrank_orthogonal_span_pair_add_two hnd hfe
  obtain ⟨m, c, hc, hcW⟩ := ih (finrank K Z) (by omega) Z rfl (B.restrict Z)
    (fun z => hB.self_eq_zero z) (hB.restrict_nondegenerate_orthogonal_span_pair hfe hnd)
    (fun j => (W j).comap Z.subtype) σ hσ
    (hB.iSup_comap_orthogonal_span_pair_eq_top hfe hσ hW horth he hf)
    (fun i j hij v hv w hw => horth i j hij v hv w hw)
  obtain ⟨b, hb, hbd⟩ := hB.exists_basis_apply_eq_J_of_basis_orthogonal_span_pair hnd hfe c hc
  refine ⟨m + 1, b, hb, ?_⟩
  rintro (x | x) <;> induction x using Fin.cases
  · exact ⟨i, by simpa [hbd] using he⟩
  · obtain ⟨j, hj⟩ := hcW (Sum.inl _)
    exact ⟨j, by simpa [hbd] using hj⟩
  · exact ⟨σ i, by simpa [hbd] using hf⟩
  · obtain ⟨j, hj⟩ := hcW (Sum.inr _)
    exact ⟨j, by simpa [hbd] using hj⟩

/-- **A nondegenerate alternating form on a compatibly graded space has a homogeneous symplectic
basis.**

Let `V` be spanned by subspaces `W i`, indexed by a type with an involution `σ`, such that `B`
pairs `W i` and `W j` trivially unless `j = σ i`. Then `V` has a basis indexed by `Fin m ⊕ Fin m`
in which the matrix of `B` is the standard symplectic matrix `Matrix.J`, every vector of which
lies in one of the `W i`. -/
theorem IsAlt.exists_basis_toMatrix_eq_J_of_iSup_eq_top {ι : Type*} {W : ι → Submodule K V}
    {σ : ι → ι} (hσ : Function.Involutive σ) (hW : ⨆ i, W i = ⊤)
    (horth : ∀ i j, j ≠ σ i → ∀ v ∈ W i, ∀ w ∈ W j, B v w = 0) :
    ∃ (m : ℕ) (b : Basis (Fin m ⊕ Fin m) K V),
      BilinForm.toMatrix b B = Matrix.J (Fin m) K ∧ ∀ x, ∃ i, b x ∈ W i := by
  obtain ⟨m, b, hb, hbW⟩ := exists_basis_apply_eq_J_of_iSup_eq_top_aux (finrank K V) V rfl B hB
    hnd W σ hσ hW horth
  exact ⟨m, b, Matrix.ext fun x y => by rw [toMatrix_apply, hb], hbW⟩

/-- **A nondegenerate alternating form has a symplectic basis**: a basis indexed by
`Fin m ⊕ Fin m` in which its matrix is the standard symplectic matrix `Matrix.J`. -/
theorem IsAlt.exists_basis_toMatrix_eq_J :
    ∃ (m : ℕ) (b : Basis (Fin m ⊕ Fin m) K V), BilinForm.toMatrix b B = Matrix.J (Fin m) K := by
  obtain ⟨m, b, hb, -⟩ := hB.exists_basis_toMatrix_eq_J_of_iSup_eq_top hnd
    (W := fun _ : Unit => (⊤ : Submodule K V)) (σ := fun i => i) (fun _ => rfl) (by simp)
    (fun _ _ h => absurd (Subsingleton.elim _ _) h)
  exact ⟨m, b, hb⟩

/-- A finite-dimensional space carrying a nondegenerate alternating form has even dimension. -/
theorem IsAlt.even_finrank : Even (finrank K V) := by
  obtain ⟨m, b, -⟩ := hB.exists_basis_toMatrix_eq_J hnd
  exact ⟨m, by rw [finrank_eq_card_basis b, Fintype.card_sum, Fintype.card_fin]⟩

end LinearMap.BilinForm
