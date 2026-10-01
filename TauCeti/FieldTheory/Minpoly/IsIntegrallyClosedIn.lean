/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.LinearDisjoint
public import Mathlib.RingTheory.Polynomial.IsIntegral

import Mathlib.FieldTheory.PrimitiveElement

/-!
# Minimal polynomials over a relatively algebraically closed base field

Let `F / k` be a field extension in which `k` is relatively algebraically closed, that is,
`IsIntegrallyClosedIn k F` — equivalently `algebraicClosure k F = ⊥` — and let `E` be a further
commutative `F`-algebra.  An element `x` of `E` algebraic over `k` then has the same minimal
polynomial over `F` as over `k`: the coefficients of `minpoly F x` are integral over `k`, because
that polynomial divides the monic polynomial `(minpoly k x).map (algebraMap k F)`, and relative
algebraic closedness puts them back into `k`.

Consequently, for `E` a field, `F⟮x⟯ / F` and `k⟮x⟯ / k` have the same degree.  This is the
mechanism behind the degree behaviour of a constant field extension: adjoining constants to `F`
costs exactly what adjoining them to `k` costs. More strongly, every separable extension
of `k` inside `E` is linearly disjoint from `F`, and a linearly independent family of separable
constants over `k` stays linearly independent over `F`.  Linear disjointness also shows that the
compositum `F · k'` with a separable extension `k'` of `k` acquires no new separable constants: an
element of `F · k'` separable over `k'` already lies in `k'`.

## Main results

* `TauCeti.minpoly.map_algebraMap_of_isIntegrallyClosedIn`: `minpoly F x` is the image of
  `minpoly k x`.
* `TauCeti.IntermediateField.finrank_adjoin_simple_eq_finrank_adjoin_simple_of_isIntegrallyClosedIn`
  : `[F⟮x⟯ : F] = [k⟮x⟯ : k]`.
* `TauCeti.linearDisjoint_fieldRange_of_isIntegrallyClosedIn`: a separable extension of `k` inside
  a common overfield is linearly disjoint from `F`.
* `TauCeti.linearIndependent_algebraMap_comp_of_isIntegrallyClosedIn`: a linearly independent
  family of separable elements stays linearly independent after extending scalars from `k` to `F`.
* `TauCeti.linearIndependent_algebraMap_comp_of_isIntegrallyClosedIn_of_isSeparable`: a linearly
  independent family in `F` stays linearly independent after extending scalars from `k` to a
  separable extension `k'`.
* `TauCeti.IntermediateField.eq_of_le_of_adjoin_le_of_isIntegrallyClosedIn`: a finite separable
  extension of `k` inside `E` is determined by its compositum with `F`.
* `TauCeti.mem_range_algebraMap_of_mem_adjoin_of_isSeparable_of_isIntegrallyClosedIn`: an element
  of the compositum `F · k'` separable over `k'` lies in `k'`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.6.  This is the field theory behind the persistence of linear independence under a
  constant field extension (Proposition 3.6.1(b)) and behind the determination of the constant
  field of a constant field extension (Proposition 3.6.1(a)); it is stated here for an arbitrary
  extension `F / k` with `k` relatively algebraically closed, with no function field involved.
-/

public section

open IntermediateField Polynomial

namespace TauCeti

universe u v w

variable {k : Type u} {F : Type v} {E : Type w} [Field k] [Field F] [Algebra k F]

section CommRing

variable [CommRing E] [Algebra k E] [Algebra F E] [IsScalarTower k F E]

/-- If `k` is relatively algebraically closed in `F`, then an element of an extension of `F` that
is algebraic over `k` has the same minimal polynomial over `F` as over `k`.

Without the hypothesis only the divisibility `minpoly F x ∣ (minpoly k x).map (algebraMap k F)`
holds; the content is that the coefficients of the left-hand factor, being integral over `k` and
lying in `F`, are constants. -/
theorem minpoly.map_algebraMap_of_isIntegrallyClosedIn (hex : IsIntegrallyClosedIn k F) {x : E}
    (hx : IsIntegral k x) : (minpoly k x).map (algebraMap k F) = minpoly F x := by
  -- make the exactness hypothesis available to instance search
  have := hex
  -- the coefficients of `minpoly F x` are integral over `k`, hence constants
  refine minpoly.map_algebraMap hx ((Polynomial.lifts_iff_coeff_lifts _).2 fun n ↦
    IsIntegrallyClosedIn.isIntegral_iff.1 ?_)
  exact Polynomial.isIntegral_coeff_of_dvd _ _ (minpoly.monic hx) (minpoly.monic hx.tower_top)
    (minpoly.dvd_map_of_isScalarTower k F x) n

end CommRing

section Field

variable [Field E] [Algebra k E] [Algebra F E] [IsScalarTower k F E]

/-- If `k` is relatively algebraically closed in `F`, then adjoining an element algebraic over `k`
to `F` raises the degree by exactly as much as adjoining it to `k` does. -/
theorem IntermediateField.finrank_adjoin_simple_eq_finrank_adjoin_simple_of_isIntegrallyClosedIn
    (hex : IsIntegrallyClosedIn k F) {x : E} (hx : IsIntegral k x) :
    Module.finrank F F⟮x⟯ = Module.finrank k k⟮x⟯ := by
  rw [adjoin.finrank hx.tower_top, adjoin.finrank hx,
    ← minpoly.map_algebraMap_of_isIntegrallyClosedIn hex hx,
    Polynomial.natDegree_map_eq_of_injective (algebraMap k F).injective]

/-! ### Linear disjointness from a separable extension -/

/-- The finite-dimensional case of `TauCeti.linearDisjoint_fieldRange_of_isIntegrallyClosedIn`,
for an intermediate field of `E / k`. -/
private theorem linearDisjoint_of_isIntegrallyClosedIn_of_finiteDimensional
    (hex : IsIntegrallyClosedIn k F) (K : IntermediateField k E) [FiniteDimensional k K]
    [Algebra.IsSeparable k K] : K.LinearDisjoint F := by
  let pb : PowerBasis k K := Field.powerBasisOfFiniteOfSeparable k K
  let x : E := pb.gen
  have hx : IsIntegral k x := pb.isIntegral_gen.map K.val
  -- exactness of `k` in `F`: the generator has the same degree over `F` as over `k`
  have hdegree : (minpoly F x).natDegree = pb.dim := by
    rw [← minpoly.map_algebraMap_of_isIntegrallyClosedIn hex hx,
      Polynomial.natDegree_map_eq_of_injective (algebraMap k F).injective,
      ← IntermediateField.minpoly_eq, pb.natDegree_minpoly]
  let b : Module.Basis (Fin (minpoly F x).natDegree) k K :=
    pb.basis.reindex (finCongr hdegree.symm)
  have hb : K.val ∘ b = fun i : Fin (minpoly F x).natDegree ↦ x ^ (i : ℕ) := by
    ext i
    simp only [Function.comp_apply, b, Module.Basis.reindex_apply, PowerBasis.coe_basis,
      finCongr_symm_apply, Fin.val_cast, IntermediateField.coe_val, IntermediateField.coe_pow, x]
  exact .of_basis_left b (hb ▸ linearIndependent_pow x)

variable {k' : Type*} [Field k'] [Algebra k k'] [Algebra k' E]
variable [IsScalarTower k k' E]

/-- A separable extension `k'` of a relatively algebraically closed field `k` is linearly
disjoint from `F` inside any common overfield `E`.

Consequently the compositum of `F` and `k'` inside `E` behaves like `F ⊗[k] k'`: for finite
`k' / k` it has degree `[k' : k]` over `F`. This is the field-theoretic content of Stichtenoth,
Proposition 3.6.1(b), for separable constant field extensions. -/
theorem linearDisjoint_fieldRange_of_isIntegrallyClosedIn
    (hex : IsIntegrallyClosedIn k F) [Algebra.IsSeparable k k'] :
    (IsScalarTower.toAlgHom k k' E).fieldRange.LinearDisjoint F := by
  set K := (IsScalarTower.toAlgHom k k' E).fieldRange
  have : Algebra.IsSeparable k K :=
    AlgEquiv.Algebra.isSeparable (IsScalarTower.toAlgHom k k' E).equivFieldRange
  let b := Module.Basis.ofVectorSpace k K
  refine .of_basis_left b (linearIndependent_iff_finset_linearIndependent.2 fun s ↦ ?_)
  -- the finitely many basis vectors indexed by `s` generate a finite separable subextension
  let K₀ : IntermediateField k E := adjoin k (Set.range fun i : s ↦ (b i : E))
  have hK₀ : K₀ ≤ K := adjoin_le_iff.2 (Set.range_subset_iff.2 fun i ↦ (b i).2)
  have : FiniteDimensional k K₀ := finiteDimensional_adjoin fun _ ⟨i, hi⟩ ↦
    hi ▸ (Algebra.IsIntegral.isIntegral (b i)).map K.val
  have : Algebra.IsSeparable k K₀ := Algebra.IsSeparable.of_algHom k K (inclusion hK₀)
  let v : s → K₀ := fun i ↦ ⟨b i, subset_adjoin k _ ⟨i, rfl⟩⟩
  have hb : LinearIndependent k (K.val ∘ b) :=
    b.linearIndependent.map' K.val.toLinearMap (LinearMap.ker_eq_bot.2 Subtype.val_injective)
  have hv : LinearIndependent k v :=
    .of_comp K₀.val.toLinearMap (hb.comp _ Subtype.val_injective)
  have h := LinearDisjoint.linearIndependent_left
    (linearDisjoint_of_isIntegrallyClosedIn_of_finiteDimensional hex K₀) hv
  convert h using 1
  ext i
  simp only [Function.comp_apply, IntermediateField.coe_val, v]

/-- A linearly independent family of separable elements over a relatively algebraically closed
field `k` remains linearly independent after extending scalars to `F` inside a common overfield.

For an algebraic function field and a separable constant field extension, this is Stichtenoth,
Proposition 3.6.1(b). -/
theorem linearIndependent_algebraMap_comp_of_isIntegrallyClosedIn
    (hex : IsIntegrallyClosedIn k F) {ι : Type*} {v : ι → k'}
    (hsep : ∀ i, IsSeparable k (v i)) (hv : LinearIndependent k v) :
    LinearIndependent F (algebraMap k' E ∘ v) := by
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  let K₀ : IntermediateField k E :=
    adjoin k (Set.range fun i : s ↦ algebraMap k' E (v i))
  have : FiniteDimensional k K₀ := finiteDimensional_adjoin fun _ ⟨i, hi⟩ ↦
    hi ▸ (hsep i).isIntegral.map (IsScalarTower.toAlgHom k k' E)
  have : Algebra.IsSeparable k K₀ := (isSeparable_adjoin_iff_isSeparable k E).2 <| by
    rintro _ ⟨i, rfl⟩
    exact (hsep i).map (IsScalarTower.toAlgHom k k' E) (algebraMap k' E).injective
  let w : s → K₀ := fun i ↦ ⟨algebraMap k' E (v i), subset_adjoin k _ ⟨i, rfl⟩⟩
  have hw : LinearIndependent k w := by
    apply LinearIndependent.of_comp K₀.val.toLinearMap
    simpa only [Function.comp_apply, w, IntermediateField.coe_val, AlgHom.toLinearMap_apply,
      IsScalarTower.toAlgHom_apply] using!
        (hv.comp Subtype.val Subtype.val_injective).map'
          (IsScalarTower.toAlgHom k k' E).toLinearMap
          (LinearMap.ker_eq_bot.2 (algebraMap k' E).injective)
  have h := LinearDisjoint.linearIndependent_left
    (linearDisjoint_of_isIntegrallyClosedIn_of_finiteDimensional hex K₀) hw
  convert h using 1
  ext i
  rfl

/-- **Linear independence over `k` persists over a separable extension `k'`** (Stichtenoth,
Proposition 3.6.1(b)): if `k` is relatively algebraically closed in `F` and `k' / k` is separable,
then a family of elements of `F` linearly independent over `k` stays linearly independent over
`k'` inside a common overfield `E`.

This is the companion of `TauCeti.linearIndependent_algebraMap_comp_of_isIntegrallyClosedIn`,
which extends scalars on the other side of the linearly disjoint pair `F`, `k'`. -/
theorem linearIndependent_algebraMap_comp_of_isIntegrallyClosedIn_of_isSeparable
    (hex : IsIntegrallyClosedIn k F) [Algebra.IsSeparable k k'] {ι : Type*} {v : ι → F}
    (hv : LinearIndependent k v) : LinearIndependent k' (algebraMap F E ∘ v) :=
  ((linearDisjoint_fieldRange_of_isIntegrallyClosedIn (E := E) hex).linearIndependent_right'
    hv).map_of_injective_injective (IsScalarTower.toAlgHom k k' E).equivFieldRange
    (AddMonoidHom.id E) (by simp) (by simp) fun _ _ ↦ by simp_rw [Algebra.smul_def]; rfl

/-! ### Constants of the compositum -/

/-- **A finite separable extension of a relatively algebraically closed field is determined by its
compositum with `F`**: if `K₀ ≤ K₁` are finite separable extensions of `k` inside `E` and the
compositum `F · K₁` is contained in `F · K₀`, then `K₀ = K₁`.

Linear disjointness gives `[F · Kᵢ : F] = [Kᵢ : k]`, so the two composita being equal forces the two
degrees over `k` to agree. -/
theorem IntermediateField.eq_of_le_of_adjoin_le_of_isIntegrallyClosedIn
    (hex : IsIntegrallyClosedIn k F) {K₀ K₁ : IntermediateField k E} [FiniteDimensional k K₁]
    [Algebra.IsSeparable k K₁] (hle : K₀ ≤ K₁)
    (h : adjoin F (K₁ : Set E) ≤ adjoin F (K₀ : Set E)) : K₀ = K₁ := by
  have : FiniteDimensional k K₀ :=
    Module.Finite.of_injective (inclusion hle).toLinearMap (inclusion_injective hle)
  have : Algebra.IsSeparable k K₀ := Algebra.IsSeparable.of_algHom k K₁ (inclusion hle)
  have h₀ := (linearDisjoint_of_isIntegrallyClosedIn_of_finiteDimensional hex
    K₀).adjoin_rank_eq_rank_left_of_isAlgebraic (.inl inferInstance)
  have h₁ := (linearDisjoint_of_isIntegrallyClosedIn_of_finiteDimensional hex
    K₁).adjoin_rank_eq_rank_left_of_isAlgebraic (.inl inferInstance)
  refine eq_of_le_of_finrank_eq hle (congrArg Cardinal.toNat ?_)
  rw [← h₀, ← h₁, le_antisymm (adjoin.mono F _ _ hle) h]

/-- **A separable constant of the compositum `F · k'` is a constant of `k'`**: if `k` is relatively
algebraically closed in `F` and `k' / k` is separable algebraic, then every element of the
compositum of `F` and `k'` inside a common overfield `E` that is separable over `k'` already lies
in `k'`.

For an algebraic function field and a separable constant field extension, this is the content of
Stichtenoth, Proposition 3.6.1(a), stated with separability of the constant in place of
perfectness of `k`; over a perfect `k` every constant is separable. -/
theorem mem_range_algebraMap_of_mem_adjoin_of_isSeparable_of_isIntegrallyClosedIn
    (hex : IsIntegrallyClosedIn k F) [Algebra.IsSeparable k k'] {z : E}
    (hz : z ∈ adjoin F (Set.range (algebraMap k' E))) (hsep : IsSeparable k' z) :
    z ∈ Set.range (algebraMap k' E) := by
  -- `z` lies in the compositum of `F` with finitely many constants `T`
  obtain ⟨T, hT, hzT⟩ := exists_finset_of_mem_adjoin hz
  have hTsep : ∀ x ∈ (T : Set E), IsSeparable k x := fun x hx ↦ by
    obtain ⟨c, rfl⟩ := hT hx
    exact (Algebra.IsSeparable.isSeparable k c).map (IsScalarTower.toAlgHom k k' E)
      (algebraMap k' E).injective
  have hsep' : ∀ x ∈ insert z (T : Set E), IsSeparable k x :=
    Set.forall_mem_insert.2 ⟨IsSeparable.of_algebra_isSeparable_of_isSeparable k hsep, hTsep⟩
  have : FiniteDimensional k (adjoin k (insert z (T : Set E))) :=
    finiteDimensional_adjoin fun x hx ↦ (hsep' x hx).isIntegral
  have : Algebra.IsSeparable k (adjoin k (insert z (T : Set E))) :=
    (isSeparable_adjoin_iff_isSeparable k E).2 hsep'
  -- adjoining `z` to `k(T)` does not change the compositum with `F`, so it does not change `k(T)`
  have hadj : adjoin k (insert z (T : Set E)) ≤
      (adjoin F (adjoin k (T : Set E) : Set E)).restrictScalars k :=
    adjoin_le_iff.2 <| Set.insert_subset_iff.2
      ⟨adjoin.mono F _ _ (subset_adjoin k _) hzT, (subset_adjoin k _).trans (subset_adjoin F _)⟩
  have heq : adjoin k (T : Set E) = adjoin k (insert z (T : Set E)) :=
    IntermediateField.eq_of_le_of_adjoin_le_of_isIntegrallyClosedIn hex
      (adjoin.mono k _ _ (Set.subset_insert z _)) (adjoin_le_iff.2 fun x hx ↦ hadj hx)
  have hle : adjoin k (T : Set E) ≤ (IsScalarTower.toAlgHom k k' E).fieldRange :=
    adjoin_le_iff.2 (by rwa [AlgHom.coe_fieldRange, IsScalarTower.coe_toAlgHom'])
  exact AlgHom.mem_fieldRange.1 (hle (heq ▸ subset_adjoin k _ (Set.mem_insert z _)))

end Field

end TauCeti
