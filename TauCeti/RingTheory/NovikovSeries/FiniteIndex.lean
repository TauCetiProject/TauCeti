/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Trace.Defs
public import TauCeti.RingTheory.NovikovSeries.Functoriality

/-!
# Novikov series over a finite-index subgroup of exponents

Let `N : H →+ ℝ` be a period homomorphism on an additive commutative group `H`, and let `K ≤ H`
be a subgroup, with the restricted period map `N.comp K.subtype`. The pushforward along the
inclusion `K → H` makes `Nov(R, H, N)` an algebra over `Nov(R, K, N|K)`; its algebra map keeps
every coefficient at its exponent (`TauCeti.NovikovSeries.coeff_algebraMap_addSubgroup_coe`). For
a finite cyclic covering, `H` is the deck group of the base and `K` that of the cover, and this
is the extension along which the norm and trace of Novikov series are taken.

The restriction of coefficients `comap K.subtype` to `K` satisfies the projection formula
`comap (b * a) = b * comap a` for `b` in `Nov(R, K, N|K)`
(`TauCeti.NovikovSeries.comap_subtype_algebraMap_mul`). Consequently, if `K` has finite index and
`s : H ⧸ K → H` picks a representative of each coset, the monomials `e^(s q)` form a basis of
`Nov(R, H, N)` over `Nov(R, K, N|K)` (`TauCeti.NovikovSeries.cosetBasis`): the coordinate at `q`
of a series `a` is the series on `K` with coefficient `a.coeff (s q + k)` at `k`. This basis is
finite, so the norm and trace of Mathlib's `Algebra.norm` and `Algebra.trace` are defined by the
determinant and trace of multiplication, with their basis independence and the multiplicativity
of the norm. Each diagonal entry of the matrix of multiplication by `a` in this basis is the
restriction of `a` to `K`, so the trace of `a` is `[H : K]` times that restriction
(`TauCeti.NovikovSeries.trace_eq_index_smul_comap`).

## Main definitions

* `TauCeti.NovikovSeries.instAlgebraAddSubgroup`: `Nov(R, H, N)` as an algebra over
  `Nov(R, K, N|K)`, along the pushforward of the inclusion of exponents.
* `TauCeti.NovikovSeries.cosetBasis`: for a finite-index subgroup `K` and coset representatives
  `s`, the basis of monomials `e^(s q)`.

## Main results

* `TauCeti.NovikovSeries.comap_subtype_algebraMap_mul`: the projection formula for restriction
  of coefficients to `K`.
* `TauCeti.NovikovSeries.cosetBasis_apply` and `TauCeti.NovikovSeries.coeff_cosetBasis_repr`:
  the basis vectors and the coefficients of the coordinates.
* `TauCeti.NovikovSeries.finrank_eq_index`: over a nontrivial commutative ring, the rank of
  `Nov(R, H, N)` over `Nov(R, K, N|K)` is the index `[H : K]`.
* `TauCeti.NovikovSeries.trace_eq_index_smul_comap`: the trace of `a` is `[H : K]` times the
  restriction of `a` to `K`.

## References

* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002),
  Section 2.
* V. Turaev, *Introduction to Combinatorial Torsions*, Birkhäuser 2001, Chapter I.
-/

public section

noncomputable section

open Finset

namespace TauCeti

namespace NovikovSeries

variable {R H : Type*} [AddCommGroup H] {N : H →+ ℝ} (K : AddSubgroup H)

/-- The inclusion of a subgroup preserves periods, for the restricted period map. -/
theorem exists_period_rescale_subtype :
    ∃ c > 0, ∀ k, N (K.subtype k) = c * (N.comp K.subtype) k :=
  ⟨1, one_pos, fun k => by simp⟩

section Algebra

variable [CommSemiring R]

/-- Novikov series on `H` form an algebra over Novikov series on a subgroup `K`, with the
restricted period map, along the pushforward of the inclusion `K → H`. -/
instance instAlgebraAddSubgroup :
    Algebra (NovikovSeries R K (N.comp K.subtype)) (NovikovSeries R H N) :=
  (mapRingHom (RingHom.id R) K.subtype (exists_period_rescale_subtype K)).toAlgebra

/-- The algebra map from Novikov series on `K` is the pushforward along the inclusion. -/
theorem algebraMap_addSubgroup_eq_mapRingHom :
    algebraMap (NovikovSeries R K (N.comp K.subtype)) (NovikovSeries R H N) =
      mapRingHom (RingHom.id R) K.subtype (exists_period_rescale_subtype K) :=
  (rfl)

variable {K}

/-- The algebra map from Novikov series on `K` keeps every coefficient at its exponent. -/
@[simp]
theorem coeff_algebraMap_addSubgroup_coe (b : NovikovSeries R K (N.comp K.subtype)) (k : K) :
    (algebraMap _ (NovikovSeries R H N) b).coeff k = b.coeff k := by
  rw [algebraMap_addSubgroup_eq_mapRingHom, mapRingHom_apply, ← AddSubgroup.subtype_apply,
    coeff_map_of_injective _ _ _ K.subtype_injective, RingHom.toAddMonoidHom_id,
    AddMonoidHom.id_apply]

/-- The algebra map from Novikov series on `K` has zero coefficients outside `K`. -/
theorem coeff_algebraMap_addSubgroup_of_notMem (b : NovikovSeries R K (N.comp K.subtype))
    {h : H} (hh : h ∉ K) : (algebraMap _ (NovikovSeries R H N) b).coeff h = 0 := by
  rw [algebraMap_addSubgroup_eq_mapRingHom, mapRingHom_apply]
  exact coeff_map_eq_zero_of_notMem_range _ K.subtype _ b (by simpa using hh)

/-- The algebra map from Novikov series on `K` sends the monomial `r e^k` to `r e^k`. -/
@[simp]
theorem algebraMap_addSubgroup_single (k : K) (r : R) :
    algebraMap (NovikovSeries R K (N.comp K.subtype)) (NovikovSeries R H N) (single k r) =
      single (k : H) r := by
  rw [algebraMap_addSubgroup_eq_mapRingHom, mapRingHom_apply, map_single, RingHom.toAddMonoidHom_id,
    AddMonoidHom.id_apply, AddSubgroup.subtype_apply]

variable (K) in
/-- The coefficient scalars act on Novikov series on `H` through Novikov series on `K`. -/
instance instIsScalarTowerAddSubgroup :
    IsScalarTower R (NovikovSeries R K (N.comp K.subtype)) (NovikovSeries R H N) :=
  .of_algebraMap_eq (S := NovikovSeries R K (N.comp K.subtype)) fun r => by
    simp only [algebraMap_apply, algebraMap_addSubgroup_single, AddSubgroup.coe_zero]

variable (hφ : ∃ c > 0, ∀ k, N (K.subtype k) = c * (N.comp K.subtype) k)
  (hker : (K.subtype.ker : Set K).Finite)

/-- Restricting the image of a Novikov series on `K` back to `K` recovers the series. -/
@[simp]
theorem comap_subtype_algebraMap (b : NovikovSeries R K (N.comp K.subtype)) :
    comap K.subtype hφ hker (algebraMap _ (NovikovSeries R H N) b) = b := by
  ext k
  rw [coeff_comap, AddSubgroup.subtype_apply, coeff_algebraMap_addSubgroup_coe]

/-- The projection formula: restriction of coefficients to `K` is linear over Novikov series
on `K`. -/
theorem comap_subtype_algebraMap_mul (b : NovikovSeries R K (N.comp K.subtype))
    (a : NovikovSeries R H N) :
    comap K.subtype hφ hker (algebraMap _ _ b * a) = b * comap K.subtype hφ hker a := by
  ext k
  rw [coeff_comap, AddSubgroup.subtype_apply, coeff_mul]
  refine (coeff_mul_eq_sum_of_injOn (F := (finite_setOf_add_eq b (comap K.subtype hφ hker a)
    k).toFinset) (f := fun p : K × K => ((p.1 : H), (p.2 : H)))
    (fun p hp => ?_) (fun u v huv hu hv => ?_) fun p _ p' _ hpp' => ?_).trans ?_
  · rw [Set.Finite.mem_toFinset] at hp
    simp only [← AddSubgroup.coe_add, hp.1]
  · have huK : u ∈ K := by_contra fun huK => hu (coeff_algebraMap_addSubgroup_of_notMem b huK)
    have hvK : v ∈ K := by
      rw [← add_sub_cancel_left u v, huv]
      exact K.sub_mem k.2 huK
    refine ⟨(⟨u, huK⟩, ⟨v, hvK⟩), (Set.Finite.mem_toFinset _).2 ⟨Subtype.ext huv, ?_, ?_⟩, rfl⟩
    · rwa [← coeff_algebraMap_addSubgroup_coe (H := H)]
    · rwa [coeff_comap]
  · simp only [Prod.mk.injEq] at hpp'
    exact Prod.ext (Subtype.ext hpp'.1) (Subtype.ext hpp'.2)
  · simp only [coeff_algebraMap_addSubgroup_coe, coeff_mul, coeff_comap, AddSubgroup.subtype_apply]

/-- Restricting to `K` a monomial `r e^g` with `g ∉ K` times a series on `K` gives zero. -/
private theorem comap_subtype_single_mul_algebraMap_of_notMem {g : H} (hg : g ∉ K) (r : R)
    (b : NovikovSeries R K (N.comp K.subtype)) :
    comap K.subtype hφ hker (single g r * algebraMap _ (NovikovSeries R H N) b) = 0 := by
  ext k
  rw [coeff_comap, coeff_single_mul, coeff_algebraMap_addSubgroup_of_notMem, mul_zero, coeff_zero]
  exact fun hk => hg (by simpa using K.sub_mem k.2 hk)

end Algebra

section Basis

variable [CommSemiring R] [K.FiniteIndex] (s : H ⧸ K → H) (hs : ∀ q, (s q : H ⧸ K) = q)

/-- The coordinates of a Novikov series on `H` in the coset decomposition along `K`: the
coordinate at `q` is the restriction to `K` of `e^(-s q) a`. -/
private def cosetEquiv :
    NovikovSeries R H N ≃ₗ[NovikovSeries R K (N.comp K.subtype)]
      (H ⧸ K → NovikovSeries R K (N.comp K.subtype)) where
  toFun a q := comap K.subtype (exists_period_rescale_subtype K) (by simp)
    (single (-s q) 1 * a)
  map_add' a a' := by
    ext1 q
    simp only [mul_add, map_add, Pi.add_apply]
  map_smul' b a := by
    ext1 q
    rw [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, Algebra.smul_def, mul_left_comm,
      comap_subtype_algebraMap_mul]
  invFun c := ∑ᶠ q, single (s q) 1 * algebraMap _ _ (c q)
  left_inv a := by
    have := Fintype.ofFinite (H ⧸ K)
    ext h
    dsimp only
    rw [finsum_eq_sum_of_fintype, coeff_sum, sum_eq_single (h : H ⧸ K)]
    · have hK : -s h + h ∈ K := QuotientAddGroup.eq.1 (hs h)
      rw [coeff_single_mul, one_mul, ← AddSubgroup.coe_mk K _ hK,
        coeff_algebraMap_addSubgroup_coe, coeff_comap, AddSubgroup.subtype_apply,
        AddSubgroup.coe_mk, coeff_single_mul_add, one_mul]
    · intro q _ hq
      rw [coeff_single_mul, coeff_algebraMap_addSubgroup_of_notMem, mul_zero]
      exact fun hK => hq (by rw [← hs q]; exact QuotientAddGroup.eq.2 hK)
    · exact fun h => absurd (mem_univ _) h
  right_inv c := by
    have := Fintype.ofFinite (H ⧸ K)
    ext1 p
    dsimp only
    rw [finsum_eq_sum_of_fintype, mul_sum, map_sum, sum_eq_single p]
    · rw [← mul_assoc, single_mul_single, neg_add_cancel, mul_one, single_zero_one, one_mul,
        comap_subtype_algebraMap]
    · intro q _ hq
      rw [← mul_assoc, single_mul_single, mul_one, comap_subtype_single_mul_algebraMap_of_notMem]
      exact fun hK => hq (by rw [← hs p, ← hs q]; exact (QuotientAddGroup.eq.2 hK).symm)
    · exact fun h => absurd (mem_univ _) h

private theorem cosetEquiv_apply (a : NovikovSeries R H N) (q : H ⧸ K) :
    cosetEquiv K s hs a q = comap K.subtype (exists_period_rescale_subtype K)
      (by simp) (single (-s q) 1 * a) :=
  rfl

private theorem cosetEquiv_symm_apply (c : H ⧸ K → NovikovSeries R K (N.comp K.subtype)) :
    (cosetEquiv K s hs).symm c = ∑ᶠ q, single (s q) 1 * algebraMap _ _ (c q) :=
  rfl

/-- For a finite-index subgroup `K` of `H` and a choice `s` of coset representatives, the
monomials `e^(s q)` form a basis of the Novikov series on `H` over the Novikov series on `K`. -/
def cosetBasis :
    Module.Basis (H ⧸ K) (NovikovSeries R K (N.comp K.subtype)) (NovikovSeries R H N) :=
  .ofEquivFun (cosetEquiv K s hs)

/-- The basis vector of `cosetBasis` at a coset `q` is the monomial `e^(s q)`. -/
@[simp]
theorem cosetBasis_apply (q : H ⧸ K) :
    (cosetBasis K s hs q : NovikovSeries R H N) = single (s q) 1 := by
  classical
  simp only [cosetBasis, Module.Basis.coe_ofEquivFun, cosetEquiv_symm_apply]
  rw [finsum_eq_single _ q fun p hp => by rw [Pi.single_eq_of_ne hp, map_zero, mul_zero],
    Pi.single_eq_same, map_one, mul_one]

/-- The coordinate of a series `a` at the coset `q` in `cosetBasis` has coefficient
`a.coeff (s q + k)` at `k`. -/
@[simp]
theorem coeff_cosetBasis_repr (a : NovikovSeries R H N) (q : H ⧸ K) (k : K) :
    ((cosetBasis K s hs).repr a q).coeff k = a.coeff (s q + k) := by
  rw [cosetBasis, Module.Basis.ofEquivFun_repr_apply, cosetEquiv_apply, coeff_comap,
    AddSubgroup.subtype_apply, ← neg_add_cancel_left (s q) k, coeff_single_mul_add, one_mul,
    add_neg_cancel_left]

/-- Over a finite-index subgroup `K`, the Novikov series on `H` form a free module. -/
instance instModuleFreeAddSubgroup :
    Module.Free (NovikovSeries R K (N.comp K.subtype)) (NovikovSeries R H N) :=
  .of_basis (cosetBasis K Quotient.out QuotientAddGroup.out_eq')

/-- Over a finite-index subgroup `K`, the Novikov series on `H` form a finite module. -/
instance instModuleFiniteAddSubgroup :
    Module.Finite (NovikovSeries R K (N.comp K.subtype)) (NovikovSeries R H N) :=
  .of_basis (cosetBasis K Quotient.out QuotientAddGroup.out_eq')

end Basis

section Ring

variable [CommRing R] [K.FiniteIndex]

/-- Over a nontrivial commutative ring, the rank of the Novikov series on `H` over those on a
finite-index subgroup `K` is the index of `K`. -/
theorem finrank_eq_index [Nontrivial R] :
    Module.finrank (NovikovSeries R K (N.comp K.subtype)) (NovikovSeries R H N) = K.index := by
  rw [Module.finrank_eq_nat_card_basis (cosetBasis K Quotient.out QuotientAddGroup.out_eq'),
    AddSubgroup.index_eq_card]

variable {K}

/-- The trace of a Novikov series `a` on `H` over the Novikov series on a finite-index subgroup
`K` is the index `[H : K]` times the restriction of `a` to `K`. -/
theorem trace_eq_index_smul_comap
    (hφ : ∃ c > 0, ∀ k, N (K.subtype k) = c * (N.comp K.subtype) k)
    (hker : (K.subtype.ker : Set K).Finite) (a : NovikovSeries R H N) :
    Algebra.trace (NovikovSeries R K (N.comp K.subtype)) (NovikovSeries R H N) a =
      K.index • comap K.subtype hφ hker a := by
  classical
  have := Fintype.ofFinite (H ⧸ K)
  let b := cosetBasis (R := R) (N := N) K Quotient.out QuotientAddGroup.out_eq'
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace, AddSubgroup.index_eq_card,
    Nat.card_eq_fintype_card, ← card_univ, ← sum_const]
  refine sum_congr rfl fun q _ => ?_
  ext k
  rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, cosetBasis_apply,
    coeff_cosetBasis_repr, coeff_comap, AddSubgroup.subtype_apply, add_comm, coeff_mul_single_add,
    mul_one]

end Ring

end NovikovSeries

end TauCeti
