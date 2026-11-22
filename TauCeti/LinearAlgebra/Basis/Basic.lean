/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.StdBasis

/-!
# Basic lemmas about bases

A vector whose coordinates in a basis vanish outside a single index is that one coordinate times
the corresponding basis vector.  This repackages `Module.Basis.repr_symm_single`, which it runs
through in the same direction, for the common situation where what one holds is a bound on the
support rather than an explicit `Finsupp.single`.

The coordinate and linear-map lemmas hold over a semiring of scalars. For a finite integer basis of
an additive group, we also express an additive map in coordinates. A ring homomorphism's values on
an integer basis cannot all vanish when its target is nontrivial. Over a ring in which `2 ≠ 0`, no
basis vector is the negative of a basis vector. For a basis indexed by a sum `ι ⊕ κ`, the linear
maps with prescribed values on the vectors indexed by `κ` are parametrized by their values on the
vectors indexed by `ι`.

## Main results

* `Module.Basis.eq_smul_of_repr_support_subset_singleton`: a vector supported on one coordinate is
  that coordinate times the corresponding basis vector.
* `Module.Basis.intertwines_of_apply`: a linear map that intertwines two endomorphisms on a basis
  intertwines them everywhere.
* `Module.Basis.coord_map_apply`: the coordinates with respect to a basis transported along a
  linear equivalence are the coordinates of the vector transported back.
* `Module.Basis.linearIndependent_coe_basis`: the vectors of a basis of a submodule `U`, viewed in
  the ambient module, are linearly independent.
* `Module.Basis.span_range_coe`: the vectors of a basis of a submodule `U`, viewed in the ambient
  module, span `U`.
* `Module.Basis.span_range_map_coe`, `Module.Basis.linearIndependent_map_coe_basis`: their images
  under a linear map `f` span the image of `U`, and are linearly independent when `f` is injective
  on `U`.
* `Module.Basis.range_eq_span_comp`: the range of a linear map is spanned by its values on a basis.
* `Module.Basis.ofSpanEq`: a linearly independent family spanning a submodule `U` is a basis of `U`.
* `Module.Basis.eq_sum_repr_smul_of_mem`: an ambient vector in a submodule `U` expands as the
  coordinate sum of any finite basis of `U`.
* `Module.Basis.repr_eq_zero_of_mem_of_notMem`: a vector of a submodule spanned by basis vectors has
  zero coordinate at every basis vector outside the submodule.
* `Module.Basis.restrict`: restricting a basis to a subset of indices whose vectors lie in a
  submodule `U`, when vectors of `U` have zero coordinates outside that subset.
* `Module.Basis.linearIndependent_of_repr_eq_single`: a family indexed by a finite set `S` of
  indices, whose `s`-th member has the coordinates of `b s` at the indices in `S`, is linearly
  independent.
* `Module.Basis.apply_eq_sum_repr_zsmul`: an additive map evaluated at a vector is the sum of its
  values on a finite integer basis, weighted by the coordinates.
* `Module.Basis.ringHom_comp_ne_zero`: the values of a ring homomorphism to a nontrivial ring on
  an integer basis do not all vanish.
* `Module.Basis.map_sum_mul_eq_map_mul_apply`: pushing a scaled finite-basis expansion of an
  algebra element through a ring homomorphism `f` when scalar multiples of the coordinates and the
  basis vectors lift through a ring homomorphism `g`.
* `Module.Basis.ne_neg`: over a ring in which `2 ≠ 0`, no basis vector is the negative of a basis
  vector.
* `Module.Basis.constrSumInrEquiv`: the linear maps with prescribed values on the basis vectors
  `b (inr j)` correspond to their values on the basis vectors `b (inl l)`.
* `Module.Basis.algebraMap_sum_mul_eq_mul` and
  `Module.Basis.algebraMap_mul_constr_eq_algebraMap_sum`: coordinate-clearing identities for a
  finite basis over an algebra `F` of a commutative semiring `T`.
-/

public section

namespace Module.Basis

variable {ι K V : Type*} [Semiring K] [AddCommMonoid V] [Module K V]

/-- **A vector whose only possibly nonzero coordinate is the `i`-th one is that coordinate times
the `i`-th basis vector.** -/
theorem eq_smul_of_repr_support_subset_singleton (b : Module.Basis ι K V) {w : V} {i : ι}
    (h : (b.repr w).support ⊆ {i}) : w = b.repr w i • b i :=
  calc w = b.repr.symm (b.repr w) := (b.repr.symm_apply_apply w).symm
    _ = b.repr.symm (Finsupp.single i (b.repr w i)) :=
        congrArg _ (Finsupp.support_subset_singleton.1 h)
    _ = b.repr w i • b i := b.repr_symm_single i _

/-- A linear map carrying one basis to another preserves the corresponding coordinates. -/
theorem repr_map_eq_of_map_basis
    {R M N ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    (b : Module.Basis ι R M) (c : Module.Basis ι R N) (f : M →ₗ[R] N)
    (hf : ∀ i, f (b i) = c i) (x : M) : c.repr (f x) = b.repr x := by
  have h : c.repr.toLinearMap ∘ₗ f = b.repr.toLinearMap := by
    apply b.ext
    intro i
    exact (congrArg c.repr (hf i)).trans
      ((c.repr_self i).trans (b.repr_self i).symm)
  exact DFunLike.congr_fun h x

/-- A coefficient of a composite is the sum of products of coefficients through a finite
intermediate basis. The multiplication order also applies over noncommutative semirings. -/
theorem repr_comp_apply_apply {κ W : Type*} [Fintype κ] [AddCommMonoid W] [Module K W]
    (b : Basis ι K V) (c : Basis κ K W) (f : V →ₗ[K] W) (g : W →ₗ[K] V) (i k : ι) :
    b.repr ((g ∘ₗ f) (b i)) k =
      ∑ j, c.repr (f (b i)) j * b.repr (g (c j)) k := by
  conv_lhs => rw [LinearMap.comp_apply, ← c.sum_repr (f (b i))]
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul]

/-- A linear map intertwines two endomorphisms if it does so on every vector of a basis. -/
theorem intertwines_of_apply {W : Type*} [AddCommMonoid W] [Module K W]
    (b : Module.Basis ι K V) (e : V →ₗ[K] W) (f : Module.End K V) (g : Module.End K W)
    (h : ∀ i, e (f (b i)) = g (e (b i))) (x : V) : e (f x) = g (e x) := by
  have hmap : e.comp f = g.comp e := by
    apply b.ext
    intro i
    simpa only [LinearMap.comp_apply] using h i
  exact LinearMap.congr_fun hmap x

/-- The coordinates with respect to the basis `b.map f` transported along a linear equivalence
`f` are the coordinates with respect to `b` of the vector transported back along `f`. Not a simp
lemma: simp already unfolds the left side through `Module.Basis.coord_apply`. -/
theorem coord_map_apply {R M M' ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid M'] [Module R M'] (b : Module.Basis ι R M) (f : M ≃ₗ[R] M') (i : ι) (x : M') :
    (b.map f).coord i x = b.coord i (f.symm x) := by
  simp only [coord_apply, map_repr, LinearEquiv.trans_apply]

/-- A family of vectors indexed by a finite set `S` of indices, whose `s`-th member has the
coordinates of `b s` at the indices in `S`, is linearly independent. -/
theorem linearIndependent_of_repr_eq_single {b : Module.Basis ι K V} {S : Finset ι} {v : S → V}
    (hv : ∀ s : S, ∀ t ∈ S, b.repr (v s) t = Finsupp.single (s : ι) 1 t) :
    LinearIndependent K v := by
  classical
  let π : V →ₗ[K] (S → K) := LinearMap.pi fun t ↦ b.coord t
  have hπ : π ∘ v = fun s ↦ Pi.single s 1 := by
    funext s t
    simp only [Function.comp_apply, π, LinearMap.pi_apply, coord_apply]
    rw [hv s t t.property]
    by_cases hst : t = s
    · simp [hst]
    · rw [Finsupp.single_eq_of_ne (fun h : (t : ι) = s ↦ hst (Subtype.ext h)),
        Pi.single_eq_of_ne hst]
  exact LinearIndependent.of_comp π (hπ ▸ Pi.linearIndependent_single_one S K)

section Submodule

variable {R M n : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {U : Submodule R M}

/-- The vectors of a basis of a submodule `U`, viewed in the ambient module, are linearly
independent. -/
theorem linearIndependent_coe_basis (b : Module.Basis n R U) :
    LinearIndependent R fun i ↦ (b i : M) :=
  b.linearIndependent.map_injOn U.subtype U.injective_subtype.injOn

/-- The vectors of a basis of a submodule `U`, viewed in the ambient module, span `U`. -/
@[simp]
theorem span_range_coe (b : Module.Basis n R U) :
    Submodule.span R (Set.range fun i ↦ (b i : M)) = U := by
  have h := congrArg (Submodule.map U.subtype) b.span_eq
  rwa [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp] at h

/-- The images under a linear map `f` of the vectors of a basis of a submodule `U`, viewed in the
ambient module, span the image of `U`. -/
@[simp]
theorem span_range_map_coe {N : Type*} [AddCommMonoid N] [Module R N] (b : Module.Basis n R U)
    (f : M →ₗ[R] N) : Submodule.span R (Set.range fun i ↦ f (b i)) = U.map f := by
  have h := congrArg (Submodule.map f) b.span_range_coe
  rwa [Submodule.map_span, ← Set.range_comp] at h

/-- The images under a linear map `f`, injective on a submodule `U`, of the vectors of a basis of
`U`, viewed in the ambient module, are linearly independent. -/
theorem linearIndependent_map_coe_basis {N : Type*} [AddCommMonoid N] [Module R N]
    (b : Module.Basis n R U) {f : M →ₗ[R] N} (hf : Set.InjOn f U) :
    LinearIndependent R fun i ↦ f (b i) :=
  b.linearIndependent_coe_basis.map_injOn f (by rwa [b.span_range_coe])

/-- The range of a linear map is spanned by its values on a basis. -/
theorem range_eq_span_comp {N : Type*} [AddCommMonoid N] [Module R N] (b : Module.Basis n R M)
    (f : M →ₗ[R] N) : LinearMap.range f = Submodule.span R (Set.range (f ∘ b)) := by
  rw [LinearMap.range_eq_map, ← b.span_eq, Submodule.map_span, ← Set.range_comp]

/-- A linearly independent family `v` spanning a submodule `U` is a basis of `U`. -/
noncomputable def ofSpanEq {v : n → M} (hv : LinearIndependent R v)
    (h : Submodule.span R (Set.range v) = U) : Module.Basis n R U :=
  (Basis.span hv).map (LinearEquiv.ofEq _ _ h)

/-- The vectors of `Module.Basis.ofSpanEq hv h`, viewed in the ambient module, are those of `v`. -/
@[simp]
theorem coe_ofSpanEq {v : n → M} (hv : LinearIndependent R v)
    (h : Submodule.span R (Set.range v) = U) (i : n) : (ofSpanEq hv h i : M) = v i := by
  simp [ofSpanEq, Basis.span_apply]

/-- An ambient vector belonging to a submodule `U` expands in any finite basis of `U`. -/
theorem eq_sum_repr_smul_of_mem [Fintype n] (b : Module.Basis n R U) {x : M} (hx : x ∈ U) :
    x = ∑ i, b.repr ⟨x, hx⟩ i • (b i : M) := by
  simpa only [map_sum, Submodule.coe_subtype, SetLike.val_smul] using
    congrArg U.subtype (b.sum_repr ⟨x, hx⟩).symm

/-- A vector of a submodule spanned by basis vectors has zero coordinate at every basis vector
outside the submodule. -/
theorem repr_eq_zero_of_mem_of_notMem (cb : Basis ι R M) {S : Submodule R M}
    (hS : S = Submodule.span R (cb '' {j | cb j ∈ S})) {j : ι} (hj : cb j ∉ S) {z : M}
    (hz : z ∈ S) : cb.repr z j = 0 := by
  by_contra hn
  exact hj ((cb.mem_span_image.mp (hS ▸ hz)) (Finsupp.mem_support_iff.mpr hn))

/-- A basis `b` restricted to a subset `s` of indices spans a submodule `U` as a basis of `U`
whenever `b i ∈ U` for all `i ∈ s` and every `x ∈ U` has zero `b`-coordinates outside `s`. -/
noncomputable def restrict (b : Basis n R M) (s : Set n) (U : Submodule R M)
    (hmem : ∀ i ∈ s, b i ∈ U) (hzero : ∀ {x : M} {i : n}, x ∈ U → i ∉ s → b.repr x i = 0) :
    Basis s R U := by
  refine ofSpanEq (b.linearIndependent.comp (↑) Subtype.val_injective) (le_antisymm ?_ ?_)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hmem i.val i.property
  · intro x hx
    rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]
    refine Submodule.sum_mem _ fun i hi ↦ Submodule.smul_mem _ _ ?_
    by_cases his : i ∈ s
    · exact Submodule.subset_span ⟨⟨i, his⟩, rfl⟩
    · exfalso
      exact Finsupp.mem_support_iff.mp hi (hzero hx his)

/-- The vectors of `Module.Basis.restrict` in the ambient module are the original basis vectors. -/
@[simp]
theorem coe_restrict (b : Basis n R M) (s : Set n) (U : Submodule R M)
    (hmem : ∀ i ∈ s, b i ∈ U) (hzero : ∀ {x : M} {i : n}, x ∈ U → i ∉ s → b.repr x i = 0)
    (i : s) : (b.restrict s U hmem hzero i : M) = b i := by
  simp [restrict]

/-- The coordinates of a vector in `Module.Basis.restrict` are its original `b`-coordinates. -/
@[simp]
theorem restrict_repr (b : Basis n R M) (s : Set n) (U : Submodule R M)
    (hmem : ∀ i ∈ s, b i ∈ U) (hzero : ∀ {x : M} {i : n}, x ∈ U → i ∉ s → b.repr x i = 0)
    (x : U) (i : s) : (b.restrict s U hmem hzero).repr x i = b.repr (x : M) i := by
  let c := b.restrict s U hmem hzero
  have hlin : (x : M) = Finsupp.linearCombination R b ((c.repr x).mapDomain (↑)) := by
    rw [Finsupp.linearCombination_mapDomain]
    have h := congrArg U.subtype (c.linearCombination_repr x).symm
    simpa only [c, Submodule.subtype_apply, Finsupp.linearCombination_apply, map_finsuppSum,
      map_smul, Function.comp_apply, coe_restrict] using h
  have hrepr : b.repr (x : M) = (c.repr x).mapDomain (↑) := by
    rw [hlin, ← Basis.repr_symm_apply, Basis.repr_symm_apply]
    exact b.repr_linearCombination _
  exact ((DFunLike.congr_fun hrepr (i : n)).trans
    (Finsupp.mapDomain_apply_of_injective Subtype.val_injective (c.repr x) i)).symm

end Submodule

/-- An additive map evaluated at a vector is the sum of its values on a finite integer basis,
weighted by the coordinates. -/
theorem apply_eq_sum_repr_zsmul {M N F : Type*} [AddCommGroup M] [AddCommGroup N]
    [FunLike F M N] [AddMonoidHomClass F M N] [Fintype ι] (b : Basis ι ℤ M) (f : F) (y : M) :
    f y = ∑ l, b.repr y l • f (b l) := by
  conv_lhs => rw [← b.sum_repr y]
  simp only [map_sum, map_zsmul]

section RingHom

variable {R S : Type*} [NonAssocRing R] [NonAssocRing S] (b : Basis ι ℤ R)

/-- The values of a ring homomorphism to a nontrivial ring on an integer basis do not all
vanish. The basis need not be finite. -/
theorem ringHom_comp_ne_zero [Nontrivial S] (ψ : R →+* S) : ⇑ψ ∘ ⇑b ≠ 0 := fun h ↦ by
  have : ψ.toAddMonoidHom.toIntLinearMap = 0 := b.ext fun l ↦ by simpa using congrFun h l
  simpa using LinearMap.congr_fun this 1

end RingHom

/-- Pushing a scaled finite-basis expansion of an `R`-algebra element `x : A` through a ring
homomorphism `f : A →+* T`: if `r'`, `c j`, and `v j` in `S` lift `f (algebraMap R A r)`,
`f (algebraMap R A (r * b.repr x j))`, and `f (b j)` along a ring homomorphism `g : S →+* T`,
then `g (∑ j, c j * v j) = g r' * f x`. -/
theorem map_sum_mul_eq_map_mul_apply {R A S T G H : Type*} [Fintype ι]
    [CommSemiring R] [Semiring A] [Algebra R A] [Semiring S] [Semiring T]
    [FunLike G S T] [RingHomClass G S T] [FunLike H A T] [RingHomClass H A T]
    (b : Basis ι R A) (g : G) (f : H)
    {x : A} {r : R} {r' : S} {c v : ι → S}
    (hr : f (algebraMap R A r) = g r')
    (hc : ∀ j, f (algebraMap R A (r * b.repr x j)) = g (c j))
    (hv : ∀ j, f (b j) = g (v j)) :
    g (∑ j, c j * v j) = g r' * f x := by
  calc
    g (∑ j, c j * v j)
        = ∑ j, g (c j) * g (v j) := by simp only [map_sum, map_mul]
      _ = ∑ j, f (algebraMap R A (r * b.repr x j)) * f (b j) := by simp only [hc, hv]
      _ = ∑ j, f (algebraMap R A r * (b.repr x j • b j)) := by
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          simp only [map_mul, Algebra.smul_def, mul_assoc]
      _ = g r' * f x := by
          rw [← map_sum, ← Finset.mul_sum, b.sum_repr, map_mul, hr]

section Ring

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- **No basis vector is the negative of a basis vector** over a ring in which `2 ≠ 0`. The
hypothesis is needed: when `2 = 0`, every vector is its own negative. -/
theorem ne_neg (b : Basis ι R M) (h2 : (2 : R) ≠ 0) (i j : ι) : b i ≠ -b j := by
  intro h
  have h' := congrArg (fun x ↦ b.repr x i) h
  simp only [repr_self, map_neg, Finsupp.coe_neg, Pi.neg_apply, Finsupp.single_eq_same] at h'
  by_cases hji : j = i
  · subst hji
    rw [Finsupp.single_eq_same] at h'
    refine h2 ?_
    rw [← one_add_one_eq_two]
    nth_rw 1 [h']
    exact neg_add_cancel 1
  · rw [Finsupp.single_eq_of_ne (Ne.symm hji), neg_zero] at h'
    exact h2 (by rw [← one_add_one_eq_two, h', add_zero])

end Ring

section SumInr

variable {κ R M N : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N] (b : Basis (ι ⊕ κ) R M) (v : κ → N)

/-- A linear map `f : M → N` with prescribed values `f (b (inr j)) = v j` on part of a basis `b` is
determined by its values on the remaining basis vectors `b (inl l)`, and these are arbitrary. -/
noncomputable def constrSumInrEquiv :
    {f : M →ₗ[R] N // ∀ j, f (b (.inr j)) = v j} ≃ (ι → N) where
  toFun f l := f.val (b (.inl l))
  invFun g := ⟨b.constr ℕ (Sum.elim g v), fun j ↦ by rw [constr_basis, Sum.elim_inr]⟩
  left_inv f := Subtype.ext <| b.ext fun i ↦ by rcases i with l | j <;> simp [f.property]
  right_inv g := funext fun l ↦ by simp

/-- The parameter of a linear map records its values on the basis vectors `b (inl l)`. -/
@[simp]
theorem constrSumInrEquiv_apply (f : {f : M →ₗ[R] N // ∀ j, f (b (.inr j)) = v j}) (l : ι) :
    b.constrSumInrEquiv v f l = f.val (b (.inl l)) :=
  (rfl)

/-- The linear map with parameter `g` sends `b (inl l)` to `g l` and `b (inr j)` to `v j`. -/
@[simp]
theorem coe_constrSumInrEquiv_symm_apply (g : ι → N) :
    ((b.constrSumInrEquiv v).symm g).val = b.constr ℕ (Sum.elim g v) :=
  (rfl)

end SumInr

section Algebra

/-- Clearing denominators of `b.repr y` by `s` expresses `algebraMap T' F' (ψ s) * φ y` as
`algebraMap T' F' (∑ j, ψ (a j) * g j)`. -/
theorem algebraMap_sum_mul_eq_mul
    {T F M T' F' ι : Type*} [CommSemiring T] [CommSemiring F] [Algebra T F]
    [Semiring M] [Algebra F M] [CommSemiring T'] [Semiring F'] [Algebra T' F']
    [Fintype ι] (b : Module.Basis ι F M)
    (ψ : T →+* T') (g : ι → T') (φ : M →+* F')
    (hφ_alg : ∀ x, φ (algebraMap F M (algebraMap T F x)) = algebraMap T' F' (ψ x))
    (hφ_b : ∀ j, φ (b j) = algebraMap T' F' (g j))
    (y : M) (s : T) (a : ι → T)
    (ha : ∀ j, algebraMap T F (a j) = s • b.repr y j) :
    algebraMap T' F' (∑ j, ψ (a j) * g j) = algebraMap T' F' (ψ s) * φ y := by
  rw [map_sum, ← b.sum_repr y, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have haj : algebraMap T F (a j) = algebraMap T F s * b.repr y j := by
    simpa only [Algebra.smul_def] using ha j
  rw [map_mul, ← hφ_alg (a j), haj, map_mul, map_mul, hφ_alg s, ← hφ_b j, mul_assoc,
    ← map_mul φ, ← Algebra.smul_def (b.repr y j) (b j)]

/-- Evaluating a linear form `b.constr F (algebraMap T F ∘ g)` after clearing denominators of
`b.repr y` by `s` yields `algebraMap T F (∑ j, a j * g j)`. -/
theorem algebraMap_mul_constr_eq_algebraMap_sum
    {T F M ι : Type*} [CommSemiring T] [CommSemiring F] [Algebra T F]
    [AddCommMonoid M] [Module F M] [Fintype ι] (b : Module.Basis ι F M) (g : ι → T)
    (y : M) (s : T) (a : ι → T)
    (ha : ∀ j, algebraMap T F (a j) = s • b.repr y j) :
    algebraMap T F s * b.constr F (fun j ↦ algebraMap T F (g j)) y =
      algebraMap T F (∑ j, a j * g j) := by
  conv_lhs => rw [← b.sum_repr y]
  rw [map_sum, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_smul, b.constr_basis, smul_eq_mul, ← mul_assoc,
    ← Algebra.smul_def s (b.repr y j), ← ha j, ← map_mul]

end Algebra

end Module.Basis
