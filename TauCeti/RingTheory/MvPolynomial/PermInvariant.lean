/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-!
# Invariant polynomials of a permutation group and their orbit-sum basis

Let `G` be a subgroup of the permutation group of the variables `σ`. A polynomial is
`G`-invariant when renaming its variables by every `g ∈ G` leaves it unchanged. The invariant
polynomials form the subalgebra `TauCeti.MvPolynomial.permInvariants R G`; for `G = ⊤` it is
Mathlib's `MvPolynomial.symmetricSubalgebra`.

Renaming by `g` carries the monomial `X^e` to `X^(e.mapDomain g)`, so `G` permutes the exponent
vectors `e : σ →₀ ℕ`, and a polynomial is invariant exactly when its coefficients are constant on
the `G`-orbits of exponents. Mathlib registers no action of permutations on `σ →₀ ℕ`
(`Finsupp.comapMulAction` is a definition, not an instance), so the orbit relation is the explicit
setoid `TauCeti.MvPolynomial.permOrbitRel G`. When `G` is finite, for instance when `σ` is
finite, every orbit is finite, and the *orbit sum* `TauCeti.MvPolynomial.orbitSum R G e`, the sum
of the monomials `X^f` with coefficient `1` over the orbit of `e`, is invariant. The orbit sums of
the distinct orbits form a basis of the invariant subalgebra over any commutative semiring
(`TauCeti.MvPolynomial.permInvariantsBasis`).

This basis is the input to the SAGBI theory of permutation invariants: for a monomial order the
leading term of an orbit sum is the monomial of the largest exponent in its orbit, which describes
the leading-exponent monoid of the invariant subalgebra
(`TauCeti.RingTheory.MvPolynomial.SAGBI.PermInvariant`).

## Main definitions

* `TauCeti.MvPolynomial.permInvariants R G`: the subalgebra of `G`-invariant polynomials.
* `TauCeti.MvPolynomial.permOrbitRel G`: the orbit relation of `G` on exponent vectors.
* `TauCeti.MvPolynomial.orbitSum R G e`: the sum of the monomials over the `G`-orbit of `e`.
* `TauCeti.MvPolynomial.permInvariantsBasis R G`: the orbit-sum basis of the invariant
  subalgebra, indexed by the `G`-orbits of exponent vectors.

## Main results

* `TauCeti.MvPolynomial.mem_permInvariants_iff_coeff`: a polynomial is invariant if and only if its
  coefficients are constant on `G`-orbits of exponents.
* `TauCeti.MvPolynomial.permInvariants_top`: the invariants of the full permutation group are the
  symmetric polynomials.
* `TauCeti.MvPolynomial.span_range_orbitSum`: the orbit sums span the invariant subalgebra.
* `TauCeti.MvPolynomial.permInvariantsBasis_repr_apply`: the coordinate of an invariant
  polynomial along the orbit sum of an orbit is the common coefficient of the monomials of that
  orbit.

## References

* B. Sturmfels, *Algorithms in Invariant Theory*, 2nd ed., Springer, 2008, §2.7.
* M. Göbel, *Computing bases for rings of permutation-invariant polynomials*, J. Symbolic Comput.
  **19** (1995), 285–291.
-/

public section

namespace TauCeti.MvPolynomial

open _root_.MvPolynomial

variable {σ : Type*} {R : Type*} [CommSemiring R]

section Invariants

variable (R) in
/-- The subalgebra of polynomials invariant under renaming the variables by every permutation in
the subgroup `G`. -/
def permInvariants (G : Subgroup (Equiv.Perm σ)) : Subalgebra R (MvPolynomial σ R) where
  carrier := {p | ∀ g ∈ G, rename g p = p}
  algebraMap_mem' r g _ := rename_C g r
  mul_mem' hp hq g hg := by rw [map_mul, hp g hg, hq g hg]
  add_mem' hp hq g hg := by rw [map_add, hp g hg, hq g hg]

variable {G H : Subgroup (Equiv.Perm σ)} {p : MvPolynomial σ R}

@[simp]
theorem mem_permInvariants : p ∈ permInvariants R G ↔ ∀ g ∈ G, rename g p = p :=
  Iff.rfl

/-- A polynomial is invariant if and only if renaming by each `g ∈ G` preserves its coefficients:
the coefficient of `X^(e.mapDomain g)` is that of `X^e`. -/
theorem mem_permInvariants_iff_forall_coeff_mapDomain :
    p ∈ permInvariants R G ↔ ∀ g ∈ G, ∀ e : σ →₀ ℕ, p.coeff (e.mapDomain g) = p.coeff e := by
  refine ⟨fun hp g hg e ↦ ?_, fun h g hg ↦ ?_⟩
  · conv_lhs => rw [← hp g hg]
    exact coeff_rename_mapDomain _ g.injective p e
  · ext e
    obtain ⟨e, rfl⟩ := Finsupp.mapDomain_surjective g.surjective e
    rw [coeff_rename_mapDomain _ g.injective, h g hg]

/-- Invariance under a larger group is a stronger condition. -/
theorem permInvariants_anti (hGH : G ≤ H) : permInvariants R H ≤ permInvariants R G :=
  fun _ hp g hg ↦ hp g (hGH hg)

@[simp]
theorem permInvariants_bot : permInvariants R (⊥ : Subgroup (Equiv.Perm σ)) = ⊤ := by
  ext p
  simp

/-- The invariants of the full permutation group are the symmetric polynomials. -/
@[simp]
theorem permInvariants_top :
    permInvariants R (⊤ : Subgroup (Equiv.Perm σ)) = symmetricSubalgebra σ R := by
  ext p
  simp [IsSymmetric]

end Invariants

section Orbit

/-- The orbit relation of a permutation group `G` on exponent vectors: `e` and `f` are related
when renaming by some `g ∈ G` carries the monomial `X^e` to `X^f`, that is,
`e.mapDomain g = f`. -/
def permOrbitRel (G : Subgroup (Equiv.Perm σ)) : Setoid (σ →₀ ℕ) where
  r e f := ∃ g ∈ G, e.mapDomain g = f
  iseqv :=
    { refl e := ⟨1, G.one_mem, by simp⟩
      symm := by
        rintro e f ⟨g, hg, rfl⟩
        exact ⟨g⁻¹, G.inv_mem hg, by simp [← Finsupp.mapDomain_comp]⟩
      trans := by
        rintro e f d ⟨g, hg, rfl⟩ ⟨h, hh, rfl⟩
        exact ⟨h * g, G.mul_mem hh hg, by rw [Equiv.Perm.coe_mul, Finsupp.mapDomain_comp]⟩ }

variable {G : Subgroup (Equiv.Perm σ)} {e f : σ →₀ ℕ}

theorem permOrbitRel_iff : permOrbitRel G e f ↔ ∃ g ∈ G, e.mapDomain g = f :=
  Iff.rfl

theorem permOrbitRel_mapDomain {g : Equiv.Perm σ} (hg : g ∈ G) (e : σ →₀ ℕ) :
    permOrbitRel G e (e.mapDomain g) :=
  ⟨g, hg, rfl⟩

/-- A polynomial is invariant if and only if its coefficients are constant on the `G`-orbits of
exponents. -/
theorem mem_permInvariants_iff_coeff {p : MvPolynomial σ R} :
    p ∈ permInvariants R G ↔ ∀ e f, permOrbitRel G e f → p.coeff e = p.coeff f := by
  rw [mem_permInvariants_iff_forall_coeff_mapDomain]
  exact ⟨fun h e f ⟨g, hg, hf⟩ ↦ hf ▸ (h g hg e).symm,
    fun h g hg e ↦ (h e _ (permOrbitRel_mapDomain hg e)).symm⟩

variable [Finite G]

variable (G) in
/-- The `G`-orbits of exponent vectors of a finite permutation group are finite. This applies in
particular to every permutation group of finitely many variables. -/
theorem finite_setOf_permOrbitRel (e : σ →₀ ℕ) : {f | permOrbitRel G e f}.Finite :=
  (Set.finite_range fun g : G ↦ e.mapDomain g).subset
    fun _ ⟨g, hg, hf⟩ ↦ ⟨⟨g, hg⟩, hf⟩

variable (R G) in
/-- The orbit sum of an exponent vector `e`: the sum of the monomials `X^f` with coefficient `1`
over the `G`-orbit of `e`. -/
noncomputable def orbitSum (e : σ →₀ ℕ) : MvPolynomial σ R :=
  ∑ f ∈ (finite_setOf_permOrbitRel G e).toFinset, monomial f 1

theorem orbitSum_def (e : σ →₀ ℕ) :
    orbitSum R G e = ∑ f ∈ (finite_setOf_permOrbitRel G e).toFinset, monomial f 1 :=
  (rfl)

@[simp]
theorem coeff_orbitSum_of_rel (h : permOrbitRel G e f) : (orbitSum R G e).coeff f = 1 := by
  classical
  rw [orbitSum, coeff_sum, Finset.sum_eq_single_of_mem f (by simpa using h)]
  · simp
  · intro d _ hd
    simp [coeff_monomial, hd]

theorem coeff_orbitSum_of_not_rel (h : ¬permOrbitRel G e f) : (orbitSum R G e).coeff f = 0 := by
  classical
  rw [orbitSum, coeff_sum]
  refine Finset.sum_eq_zero fun d hd ↦ ?_
  have hdf : d ≠ f := by
    rintro rfl
    exact h (by simpa using hd)
  simp [coeff_monomial, hdf]

theorem coeff_orbitSum [Decidable (permOrbitRel G e f)] :
    (orbitSum R G e).coeff f = if permOrbitRel G e f then 1 else 0 := by
  split_ifs with h
  · exact coeff_orbitSum_of_rel h
  · exact coeff_orbitSum_of_not_rel h

/-- The monomials of an orbit sum are those of the orbit. -/
theorem mem_support_orbitSum [Nontrivial R] :
    f ∈ (orbitSum R G e).support ↔ permOrbitRel G e f := by
  by_cases h : permOrbitRel G e f
  · simp [h, coeff_orbitSum_of_rel h]
  · simp [h, coeff_orbitSum_of_not_rel h]

@[simp]
theorem orbitSum_ne_zero [Nontrivial R] : orbitSum R G e ≠ 0 :=
  ne_zero_iff.2 ⟨e, by
    rw [coeff_orbitSum_of_rel ((permOrbitRel G).refl' e)]
    exact one_ne_zero⟩

/-- An orbit sum has the same coefficient at exponents in the same orbit. -/
theorem coeff_orbitSum_eq_of_rel {d d' : σ →₀ ℕ} (h : permOrbitRel G d d') :
    (orbitSum R G e).coeff d = (orbitSum R G e).coeff d' := by
  by_cases hd : permOrbitRel G e d
  · rw [coeff_orbitSum_of_rel hd, coeff_orbitSum_of_rel ((permOrbitRel G).trans' hd h)]
  · rw [coeff_orbitSum_of_not_rel hd, coeff_orbitSum_of_not_rel fun h' ↦
      hd ((permOrbitRel G).trans' h' ((permOrbitRel G).symm' h))]

/-- The coefficient of `X^f` in the orbit sum of `e` is that of `X^e` in the orbit sum of `f`. -/
theorem coeff_orbitSum_comm : (orbitSum R G e).coeff f = (orbitSum R G f).coeff e := by
  by_cases h : permOrbitRel G e f
  · rw [coeff_orbitSum_of_rel h, coeff_orbitSum_of_rel ((permOrbitRel G).symm' h)]
  · rw [coeff_orbitSum_of_not_rel h, coeff_orbitSum_of_not_rel (mt (permOrbitRel G).symm' h)]

/-- Exponents in the same orbit have the same orbit sum. -/
theorem orbitSum_eq_of_rel (h : permOrbitRel G e f) : orbitSum R G e = orbitSum R G f := by
  ext d
  rw [coeff_orbitSum_comm, coeff_orbitSum_eq_of_rel h, coeff_orbitSum_comm]

/-- Over nontrivial coefficients, two orbit sums agree exactly when the exponents lie in the same
orbit. -/
@[simp]
theorem orbitSum_eq_orbitSum_iff [Nontrivial R] :
    orbitSum R G e = orbitSum R G f ↔ permOrbitRel G e f := by
  refine ⟨fun h ↦ ?_, orbitSum_eq_of_rel⟩
  have hf : f ∈ (orbitSum R G f).support :=
    mem_support_orbitSum.2 ((permOrbitRel G).refl' f)
  rwa [← h, mem_support_orbitSum] at hf

theorem orbitSum_mem_permInvariants (e : σ →₀ ℕ) : orbitSum R G e ∈ permInvariants R G :=
  mem_permInvariants_iff_coeff.2 fun _ _ ↦ coeff_orbitSum_eq_of_rel

/-- The orbit sum of a representative of an orbit `O` has coefficient `0` at every exponent outside
`O`. -/
private theorem coeff_orbitSum_out_of_ne {O : Quotient (permOrbitRel G)} {d : σ →₀ ℕ}
    (h : O ≠ ⟦d⟧) : (orbitSum R G O.out).coeff d = 0 :=
  coeff_orbitSum_of_not_rel (mt Quotient.eq_mk_iff_out.2 h)

open Classical in
/-- An invariant polynomial is the combination of the orbit sums of the orbits meeting its
support, with coefficient the common coefficient of the monomials of each orbit. -/
private theorem eq_sum_orbitSum_of_mem_permInvariants {p : MvPolynomial σ R}
    (hp : p ∈ permInvariants R G) :
    p = ∑ O ∈ p.support.image (Quotient.mk (permOrbitRel G)),
      p.coeff O.out • orbitSum R G O.out := by
  have hcoeff := mem_permInvariants_iff_coeff.1 hp
  ext d
  have hd : (p.coeff (⟦d⟧ : Quotient (permOrbitRel G)).out •
      orbitSum R G (⟦d⟧ : Quotient (permOrbitRel G)).out).coeff d = p.coeff d := by
    rw [AddMonoidAlgebra.coeff_smul_apply, coeff_orbitSum_of_rel (Quotient.mk_out d), smul_eq_mul,
      mul_one, hcoeff _ _ (Quotient.mk_out d)]
  rw [coeff_sum, Finset.sum_eq_single (Quotient.mk (permOrbitRel G) d)]
  · exact hd.symm
  · intro O _ hO
    rw [AddMonoidAlgebra.coeff_smul_apply, coeff_orbitSum_out_of_ne hO, smul_zero]
  · intro hmem
    rw [hd]
    by_contra hne
    exact hmem (Finset.mem_image_of_mem _ (mem_support_iff.2 hne))

variable (R G) in
/-- The orbit sums span the invariant subalgebra. -/
theorem span_range_orbitSum :
    Submodule.span R (Set.range (orbitSum R G)) = Subalgebra.toSubmodule (permInvariants R G) := by
  refine le_antisymm (Submodule.span_le.2 ?_) fun p hp ↦ ?_
  · rintro _ ⟨e, rfl⟩
    exact orbitSum_mem_permInvariants e
  · rw [eq_sum_orbitSum_of_mem_permInvariants hp]
    exact Submodule.sum_mem _ fun O _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

variable (R G) in
/-- The orbit sum of an orbit of exponent vectors, as an invariant polynomial. -/
private noncomputable def orbitSumQuotient (O : Quotient (permOrbitRel G)) : permInvariants R G :=
  ⟨orbitSum R G O.out, orbitSum_mem_permInvariants _⟩

private theorem coe_orbitSumQuotient (O : Quotient (permOrbitRel G)) :
    (orbitSumQuotient R G O : MvPolynomial σ R) = orbitSum R G O.out :=
  rfl

/-- The coefficient of the monomial `X^(O.out)` in a combination of orbit sums is the coefficient
of the orbit `O`. -/
private theorem coeff_linearCombination_orbitSumQuotient (c : Quotient (permOrbitRel G) →₀ R)
    (O : Quotient (permOrbitRel G)) :
    ((Finsupp.linearCombination R (orbitSumQuotient R G) c : permInvariants R G) :
      MvPolynomial σ R).coeff O.out = c O := by
  classical
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, AddSubmonoidClass.coe_finsetSum,
    coeff_sum, SetLike.val_smul, AddMonoidAlgebra.coeff_smul_apply]
  rw [Finset.sum_eq_single O]
  · rw [coe_orbitSumQuotient, coeff_orbitSum_of_rel ((permOrbitRel G).refl' _), smul_eq_mul,
      mul_one]
  · intro O' _ hO'
    rw [coe_orbitSumQuotient, coeff_orbitSum_out_of_ne (by rwa [Quotient.out_eq]), smul_zero]
  · intro hO
    rw [Finsupp.notMem_support_iff.1 hO, zero_smul]

private theorem linearIndependent_orbitSumQuotient :
    LinearIndependent R (orbitSumQuotient R G) :=
  linearIndependent_iffₛ.2 fun l₁ l₂ h ↦ Finsupp.ext fun O ↦ by
    rw [← coeff_linearCombination_orbitSumQuotient l₁,
      ← coeff_linearCombination_orbitSumQuotient l₂, h]

variable (R G) in
/-- The orbit-sum basis of the invariant subalgebra of a permutation group, indexed by the orbits
of exponent vectors: the basis vector of an orbit is the sum of its monomials. -/
noncomputable def permInvariantsBasis :
    Module.Basis (Quotient (permOrbitRel G)) R (permInvariants R G) :=
  .mk linearIndependent_orbitSumQuotient fun p _ ↦ by
    classical
    have hp : p = ∑ O ∈ (p : MvPolynomial σ R).support.image (Quotient.mk _),
        (p : MvPolynomial σ R).coeff O.out • orbitSumQuotient R G O := by
      refine Subtype.ext ((eq_sum_orbitSum_of_mem_permInvariants p.property).trans ?_)
      rw [AddSubmonoidClass.coe_finsetSum]
      simp only [SetLike.val_smul, coe_orbitSumQuotient]
    rw [hp]
    exact Submodule.sum_mem _ fun O _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨O, rfl⟩)

private theorem coe_permInvariantsBasis_eq :
    ⇑(permInvariantsBasis R G) = orbitSumQuotient R G :=
  funext fun _ ↦ Module.Basis.mk_apply _ _ _

theorem coe_permInvariantsBasis (O : Quotient (permOrbitRel G)) :
    (permInvariantsBasis R G O : MvPolynomial σ R) = orbitSum R G O.out := by
  rw [coe_permInvariantsBasis_eq, coe_orbitSumQuotient]

/-- The coordinate of an invariant polynomial along the orbit sum of an orbit is the common
coefficient of the monomials of that orbit. -/
@[simp]
theorem permInvariantsBasis_repr_apply (p : permInvariants R G) (O : Quotient (permOrbitRel G)) :
    (permInvariantsBasis R G).repr p O = (p : MvPolynomial σ R).coeff O.out := by
  conv_rhs => rw [← (permInvariantsBasis R G).linearCombination_repr p, coe_permInvariantsBasis_eq]
  exact (coeff_linearCombination_orbitSumQuotient _ O).symm

@[simp]
theorem coe_permInvariantsBasis_mk (e : σ →₀ ℕ) :
    (permInvariantsBasis R G (Quotient.mk _ e) : MvPolynomial σ R) = orbitSum R G e := by
  rw [coe_permInvariantsBasis]
  exact orbitSum_eq_of_rel (Quotient.mk_out e)

end Orbit

end TauCeti.MvPolynomial
