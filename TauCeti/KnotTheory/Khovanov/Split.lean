/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Bilinear
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.Logic.Equiv.Bool
public import TauCeti.KnotTheory.Khovanov.CircleTensor
public import TauCeti.Logic.Basic

/-!
# Split maps on circle tensors

The Frobenius pairing on a circle pairs `1` with `X` and `X` with `1`. On a finite set
of circles it therefore pairs a labelling with its pointwise complement. We construct this
perfect pairing using `Module.Basis.equiv` and `Module.Basis.dualBasis`, and define the split
map along a map of circle sets as the adjoint of `PiTensorProduct.fiberwiseMul`.

This construction retains all unaffected circles and makes no choice of circle order. Its
coefficient formula is the transpose of the merge formula with both labellings complemented.
Composition is contravariant: successive splittings correspond to composition of the maps
collapsing the output circles. Empty fibres give deaths, dual to the births of the merge map.

The pairing is the Frobenius form of the algebra `⨂ R[ε]`: it reads the `X ⊗ ⋯ ⊗ X` coordinate of
the product. Consequently the split map along `f` satisfies the projection formula
`Δ_f (m_f x * z) = x * Δ_f z`, the Frobenius identity `Δ(a b) = (a ⊗ 1) Δ(b)` for fibres. This
reduces composites of merges and splits to multiplication by merged splits of the unit; in
particular, merging and splitting around a commuting square of circle correspondences agree when
those splits of the unit agree.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §2.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*,
  Algebr. Geom. Topol. 2 (2002), §2.
-/

public section

open PiTensorProduct DualNumber TrivSqZeroExt Finset

namespace TauCeti.Khovanov

section Semiring

variable (R : Type*) [CommSemiring R] (ι : Type*) [Fintype ι]

/-- The perfect Frobenius pairing of a finite circle tensor: complementary labellings are
paired with coefficient one and all other pairs with coefficient zero. -/
noncomputable def circleDuality : CircleTensor R ι ≃ₗ[R] Module.Dual R (CircleTensor R ι) :=
  (circleBasis R ι).equiv (circleBasis R ι).dualBasis
    (Equiv.piCongrRight fun _ ↦ Equiv.boolNot)

variable {R ι}

/-- Pairing a tensor with a basis labelling reads its complementary coordinate. -/
@[simp↓]
theorem circleDuality_apply_circleBasis (x : CircleTensor R ι) (l : ι → Bool) :
    circleDuality R ι x (circleBasis R ι l) =
      (circleBasis R ι).repr x (fun i ↦ !l i) := by
  classical
  have he (k : ι → Bool) :
      (Equiv.piCongrRight fun _ : ι ↦ Equiv.boolNot) k = l ↔ k = fun i ↦ !l i :=
    (Equiv.eq_symm_apply _).symm
  rw [← (circleBasis R ι).sum_repr x]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    circleDuality, Module.Basis.equiv_apply, Module.Basis.dualBasis_apply,
    Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
  simp_rw [eq_comm (a := l), he]
  simp

/-- On the labelling basis, the circle pairing is the tensor product of the original
Frobenius forms `(a, b) ↦ counit (a * b)`. -/
theorem circleDuality_circleBasis (l k : ι → Bool) :
    circleDuality R ι (circleBasis R ι l) (circleBasis R ι k) =
      ∏ i, Coalgebra.counit (R := R) (labelBasis R (l i) * labelBasis R (k i)) := by
  classical
  rw [circleDuality_apply_circleBasis, Module.Basis.repr_self, Finsupp.single_apply]
  have hf (i : ι) :
      Coalgebra.counit (R := R) (labelBasis R (l i) * labelBasis R (k i)) =
        if l i = !k i then 1 else 0 := by
    cases l i <;> cases k i <;> simp
  simp_rw [hf]
  simp [Finset.prod_boole, funext_iff]

/-- The circle pairing is the Frobenius form of the algebra `⨂ R[ε]`: it pairs `x` and `y` by
reading the coordinate of `x * y` along the labelling with `X` on every circle. This is the
tensor product of the original counits. -/
theorem circleDuality_apply_eq_repr_mul (x y : CircleTensor R ι) :
    circleDuality R ι x y = (circleBasis R ι).repr (x * y) fun _ ↦ true := by
  have := LinearMap.ext_basis (circleBasis R ι) (circleBasis R ι)
    (B := (circleDuality R ι).toLinearMap)
    (B' := (Algebra.lmul R (CircleTensor R ι)).toLinearMap.compr₂
      ((Finsupp.lapply fun _ ↦ true) ∘ₗ (circleBasis R ι).repr.toLinearMap)) fun l k ↦ by
    rw [LinearEquiv.coe_coe, circleDuality_circleBasis]
    simp [tprod_mul_tprod]
  exact DFunLike.congr_fun (DFunLike.congr_fun this x) y

/-- The split map along `f`, adjoint to multiplication along its fibres. It maps the tensor
on `τ` to the tensor on `σ`; a two-element fibre splits that circle. -/
noncomputable def fiberwiseSplit {σ τ : Type*} [Fintype σ] [Fintype τ] [DecidableEq τ]
    (f : σ → τ) : CircleTensor R τ →ₗ[R] CircleTensor R σ :=
  (circleDuality R σ).symm.toLinearMap ∘ₗ
    (fiberwiseMul (R := R) (A := fun _ ↦ R[ε]) f).toLinearMap.dualMap ∘ₗ
      (circleDuality R τ).toLinearMap

variable {σ τ υ : Type*} [Fintype σ] [Fintype τ] [DecidableEq τ]

/-- The split map is characterized by adjunction for the Frobenius pairing. -/
@[simp]
theorem circleDuality_fiberwiseSplit (f : σ → τ) (x : CircleTensor R τ)
    (y : CircleTensor R σ) :
    circleDuality R σ (fiberwiseSplit f x) y =
      circleDuality R τ x (fiberwiseMul (R := R) (A := fun _ ↦ R[ε]) f y) := by
  simp [fiberwiseSplit, LinearMap.dualMap_apply]

/-- The `l`-coordinate of the split of `x` is the pairing of `x` with the merge of the basis
tensor labelled by the pointwise complement of `l`. -/
theorem circleBasis_repr_fiberwiseSplit_eq_circleDuality
    (f : σ → τ) (x : CircleTensor R τ) (l : σ → Bool) :
    (circleBasis R σ).repr (fiberwiseSplit f x) l =
      circleDuality R τ x
        (fiberwiseMul (R := R) (A := fun _ ↦ R[ε]) f
          (circleBasis R σ fun i ↦ !l i)) := by
  rw [← circleDuality_fiberwiseSplit, circleDuality_apply_circleBasis]
  simp

/-- The coefficient formula for arbitrary splittings and deaths. At most one output in each
fibre may carry `1`; a fibre carrying only `X` requires an input `X`, and a fibre carrying one
`1` requires an input `1`. An empty fibre also requires an input `X`. -/
theorem circleBasis_repr_fiberwiseSplit (f : σ → τ) (x : CircleTensor R τ) (l : σ → Bool) :
    (circleBasis R σ).repr (fiberwiseSplit f x) l =
      if ∀ j, #{i | f i = j ∧ (!l i) = true} ≤ 1 then
        (circleBasis R τ).repr x
          (fun j ↦ !decide (∃ i, f i = j ∧ (!l i) = true))
      else 0 := by
  classical
  rw [circleBasis_repr_fiberwiseSplit_eq_circleDuality, fiberwiseMul_circleBasis]
  split_ifs
  · exact circleDuality_apply_circleBasis _ _
  · exact map_zero _

/-- The identity correspondence gives the identity split map. -/
@[simp]
theorem fiberwiseSplit_id [DecidableEq σ] :
    fiberwiseSplit (R := R) (id : σ → σ) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply (circleDuality R σ).injective
  apply LinearMap.ext
  intro y
  simp

/-- Splitting successively is splitting along the composite circle correspondence. -/
theorem fiberwiseSplit_comp [Fintype υ] [DecidableEq υ] (g : τ → υ) (f : σ → τ) :
    (fiberwiseSplit (R := R) f).comp (fiberwiseSplit g) = fiberwiseSplit (g ∘ f) := by
  apply LinearMap.ext
  intro x
  apply (circleDuality R σ).injective
  apply LinearMap.ext
  intro y
  simp only [LinearMap.comp_apply, circleDuality_fiberwiseSplit]
  rw [← AlgHom.comp_apply, fiberwiseMul_comp]

/-- Along a bijection the split map is inverse reindexing, so relabelling circles introduces
neither a scalar nor a sign. -/
theorem fiberwiseSplit_equiv (e : σ ≃ τ) :
    fiberwiseSplit (R := R) e = (reindex R (fun _ ↦ R[ε]) e.symm).toLinearMap := by
  classical
  refine (circleBasis R τ).ext fun l ↦ (circleBasis R σ).ext_elem fun k ↦ ?_
  rw [circleBasis_repr_fiberwiseSplit_eq_circleDuality, ← AlgHom.toLinearMap_apply,
    toLinearMap_fiberwiseMul_equiv]
  simp only [LinearEquiv.coe_coe, reindex_circleBasis, circleDuality_apply_circleBasis,
    Function.comp_apply, Bool.not_not]
  simp only [Module.Basis.repr_self, Finsupp.single_apply]
  have he : (l = fun i ↦ k (e.symm i)) ↔ l ∘ e = k := e.eq_comp_symm l k
  simp only [Equiv.symm_symm, he]

/-- **The projection formula.** The split map along `f : σ → τ` is linear over the algebra of
the circles `σ`, which acts on the tensor over `τ` through multiplication along `f`. For a single
splitting this is the Frobenius identity `Δ(a b) = (a ⊗ 1) Δ(b)`. -/
theorem fiberwiseSplit_fiberwiseMul_mul (f : σ → τ) (x : CircleTensor R σ)
    (z : CircleTensor R τ) :
    fiberwiseSplit f (fiberwiseMul (A := fun _ ↦ R[ε]) f x * z) = x * fiberwiseSplit f z := by
  apply (circleDuality R σ).injective
  refine LinearMap.ext fun w ↦ ?_
  calc circleDuality R σ (fiberwiseSplit f (fiberwiseMul f x * z)) w
      = circleDuality R τ z (fiberwiseMul (A := fun _ ↦ R[ε]) f (x * w)) := by
        rw [circleDuality_fiberwiseSplit, circleDuality_apply_eq_repr_mul,
          circleDuality_apply_eq_repr_mul, map_mul (fiberwiseMul f)]
        congr 2
        ring
    _ = circleDuality R σ (x * fiberwiseSplit f z) w := by
        rw [← circleDuality_fiberwiseSplit, circleDuality_apply_eq_repr_mul,
          circleDuality_apply_eq_repr_mul]
        congr 2
        ring

section Square

variable {ρ : Type*} [Fintype ρ] [DecidableEq σ]

/-- **Splitting and then merging along a factorization.** Split along a surjection `f` and then
merge along `g = h ∘ f`, which merges every circle split off by `f` back together. The result is
multiplication by the merge of the split of `1`, after merging along `h`. -/
theorem fiberwiseMul_fiberwiseSplit [DecidableEq υ] {f : ρ → σ} (hf : Function.Surjective f)
    {g : ρ → υ} {h : σ → υ} (hgh : h ∘ f = g) (x : CircleTensor R σ) :
    fiberwiseMul (A := fun _ ↦ R[ε]) g (fiberwiseSplit f x) =
      fiberwiseMul (A := fun _ ↦ R[ε]) h x *
        fiberwiseMul (A := fun _ ↦ R[ε]) g (fiberwiseSplit f 1) := by
  classical
  subst hgh
  conv_lhs => rw [← fiberwiseMul_fiberwiseMul_surjInv hf x, ← mul_one (fiberwiseMul f _),
    fiberwiseSplit_fiberwiseMul_mul, map_mul, ← AlgHom.comp_apply, fiberwiseMul_comp,
    Function.comp_assoc, Function.comp_surjInv, Function.comp_id]

/-- **The Frobenius relation for a commuting square of circle correspondences.** Let
`f ∘ f' = g ∘ g'`, with `f'` surjective, and suppose that splitting `1` along `f'` and merging
along `g'` gives the split of `1` along `g`. Then merging along `f` and splitting along `g` is
splitting along `f'` and merging along `g'`. -/
theorem fiberwiseSplit_fiberwiseMul_of_comp_eq [Fintype υ] [DecidableEq υ] {f' : ρ → σ}
    (hf' : Function.Surjective f') {g' : ρ → υ} {f : σ → τ} {g : υ → τ}
    (hcomm : f ∘ f' = g ∘ g')
    (hone : fiberwiseMul (A := fun _ ↦ R[ε]) g' (fiberwiseSplit f' 1) =
      fiberwiseSplit (R := R) g 1) (x : CircleTensor R σ) :
    fiberwiseSplit g (fiberwiseMul (A := fun _ ↦ R[ε]) f x) =
      fiberwiseMul (A := fun _ ↦ R[ε]) g' (fiberwiseSplit f' x) := by
  classical
  have hf : f = g ∘ (g' ∘ Function.surjInv hf') := by
    rw [← Function.comp_assoc, ← hcomm, Function.comp_assoc, Function.comp_surjInv,
      Function.comp_id]
  have hrhs : fiberwiseMul (A := fun _ ↦ R[ε]) g' (fiberwiseSplit f' x) =
      fiberwiseMul (A := fun _ ↦ R[ε]) (g' ∘ Function.surjInv hf') x * fiberwiseSplit g 1 := by
    conv_lhs => rw [← fiberwiseMul_fiberwiseMul_surjInv hf' x, ← mul_one (fiberwiseMul f' _),
      fiberwiseSplit_fiberwiseMul_mul, map_mul, hone, ← AlgHom.comp_apply, fiberwiseMul_comp]
  rw [hrhs, hf, ← fiberwiseMul_comp, AlgHom.comp_apply, ← mul_one (fiberwiseMul g _),
    fiberwiseSplit_fiberwiseMul_mul]

end Square

/-- Merging and then splitting through a set of circles depends on that set only up to a
bijection compatible with both correspondences. -/
theorem fiberwiseSplit_comp_fiberwiseMul_equiv_comp [Fintype υ] {τ' : Type*} [Fintype τ']
    [DecidableEq τ'] (e : τ ≃ τ') (f : σ → τ) (g : υ → τ) :
    fiberwiseSplit (R := R) (e ∘ g) ∘ₗ (fiberwiseMul (A := fun _ ↦ R[ε]) (e ∘ f)).toLinearMap =
      fiberwiseSplit g ∘ₗ (fiberwiseMul (A := fun _ ↦ R[ε]) f).toLinearMap := by
  rw [← fiberwiseSplit_comp, ← fiberwiseMul_comp, AlgHom.comp_toLinearMap,
    toLinearMap_fiberwiseMul_equiv, fiberwiseSplit_equiv, ← reindex_symm]
  refine LinearMap.ext fun x ↦ ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

/-- Splitting `1` into two circles gives `1 ⊗ X + X ⊗ 1`; splitting `X` gives `X ⊗ X`.
The two output circles are indexed by `Bool`, and the input by `Unit`. -/
theorem fiberwiseSplit_const_circleBasis (b : Bool) :
    fiberwiseSplit (R := R) (fun _ : Bool ↦ ())
      (circleBasis R Unit fun _ ↦ b) =
        if b then circleBasis R Bool (fun _ ↦ true)
        else circleBasis R Bool id + circleBasis R Bool not := by
  classical
  apply (circleBasis R Bool).ext_elem
  intro l
  rw [circleBasis_repr_fiberwiseSplit]
  have hl : l = fun i ↦ bif i then l true else l false := by
    funext i
    cases i <;> rfl
  rw [hl]
  generalize l false = b₀, l true = b₁
  cases b <;> cases b₀ <;> cases b₁ <;>
    simp [Fintype.univ_bool, Finset.filter_insert, Finset.filter_singleton]

/-- Splitting along a surjection whose only non-singleton fibre is `{p, q}` obeys
`Δ X = X ⊗ X` and `Δ 1 = X ⊗ 1 + 1 ⊗ X` on the circles `p` and `q`; every other circle retains
the label of its image. -/
theorem fiberwiseSplit_circleBasis_of_eq_iff [DecidableEq σ] {f : σ → τ}
    (hf : Function.Surjective f) {p q : σ} (hpq : p ≠ q)
    (hfeq : ∀ a b, f a = f b ↔ a = b ∨ (a = p ∨ a = q) ∧ (b = p ∨ b = q)) (l : τ → Bool) :
    fiberwiseSplit f (circleBasis R τ l) =
      if l (f p) then circleBasis R σ fun i ↦ l (f i)
      else circleBasis R σ (Function.update (fun i ↦ l (f i)) p true) +
        circleBasis R σ (Function.update (fun i ↦ l (f i)) q true) := by
  have hfq : f q = f p := (hfeq q p).mpr (Or.inr ⟨Or.inr rfl, Or.inl rfl⟩)
  refine (circleBasis R σ).ext_elem fun k ↦ ?_
  -- At most one of the two output circles carries `1`.
  have hcount : (∀ j, #{i | f i = j ∧ (!k i) = true} ≤ 1) ↔ (k p || k q) = true := by
    refine ⟨fun h ↦ ?_, fun h j ↦ card_le_one.mpr fun a ha b hb ↦ ?_⟩
    · by_contra hk
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hk
      exact hpq (card_le_one.mp (h (f p)) p (by simp [hk.1]) q (by simp [hfq, hk.2]))
    · simp only [mem_filter, mem_univ, true_and] at ha hb
      rcases (hfeq a b).mp (ha.1.trans hb.1.symm) with hab | ⟨rfl | rfl, rfl | rfl⟩ <;> simp_all
  -- The input is `X` exactly when both outputs are, and every other circle keeps its label.
  have hlabel : (l = fun j ↦ !decide (∃ i, f i = j ∧ (!k i) = true)) ↔
      (∀ i, i ≠ p → i ≠ q → l (f i) = k i) ∧ l (f p) = (k p && k q) := by
    rw [funext_iff, hf.forall, forall_iff_forall_ne_ne_and p q, hfq, and_self]
    refine and_congr (forall_congr' fun i ↦ imp_congr_right fun hip ↦ imp_congr_right fun hiq ↦ ?_)
      ?_
    · simp [hfeq, hip, hiq]
    · simp [hfeq, or_and_right, exists_or]
  have hk (u : σ → Bool) : u = k ↔ (∀ i, i ≠ p → i ≠ q → u i = k i) ∧ u p = k p ∧ u q = k q := by
    rw [funext_iff, forall_iff_forall_ne_ne_and p q]
  have hupd (r : σ) (hr : r = p ∨ r = q) :
      (∀ i, i ≠ p → i ≠ q → Function.update (fun i ↦ l (f i)) r true i = k i) ↔
        ∀ i, i ≠ p → i ≠ q → l (f i) = k i :=
    forall_congr' fun i ↦ imp_congr_right fun hip ↦ imp_congr_right fun hiq ↦ by
      rw [Function.update_of_ne (by rcases hr with rfl | rfl <;> assumption)]
  rw [circleBasis_repr_fiberwiseSplit]
  simp only [hcount, Module.Basis.repr_self, Finsupp.single_apply, hlabel, hk, hupd p (.inl rfl),
    hupd q (.inr rfl), apply_ite (circleBasis R σ).repr,
    apply_ite (fun x : (σ → Bool) →₀ R ↦ x k), map_add, Finsupp.add_apply,
    Function.update_self, Function.update_of_ne hpq, Function.update_of_ne hpq.symm, hfq]
  -- What remains depends only on the agreement away from `p` and `q` and on three labels.
  by_cases hagree : ∀ i, i ≠ p → i ≠ q → l (f i) = k i
  · simp only [eq_true hagree, true_and]
    generalize k p = a, k q = b, l (f p) = d
    cases a <;> cases b <;> cases d <;> simp
  · simp [eq_false hagree]

end Semiring

section Grading

variable (R : Type*) [CommRing R]
variable {σ τ : Type*} [Fintype σ] [Fintype τ] [DecidableEq τ]

/-- Splitting along `f : σ → τ` has quantum degree `|τ| - |σ|`. Thus an elementary split has
degree `-1`, and deleting a circle by the counit has degree `+1`. -/
theorem isHomogeneous_fiberwiseSplit (f : σ → τ) :
    TauCeti.LinearMap.IsHomogeneous (fiberwiseSplit (R := R) f)
      (circleQuantumGrading R τ).piece (circleQuantumGrading R σ).piece
      (Fintype.card τ - Fintype.card σ) := by
  classical
  rw [TauCeti.LinearMap.isHomogeneous_def]
  intro p x hx
  rw [mem_circleQuantumGrading_piece_iff] at hx ⊢
  intro l hl
  rw [circleBasis_repr_fiberwiseSplit] at hl
  split_ifs at hl with h
  · have hd := labelingQuantumDegree_merge h
    have hp := hx _ hl
    rw [labelingQuantumDegree_not] at hd hp
    omega
  · exact (hl rfl).elim

end Grading

end TauCeti.Khovanov
