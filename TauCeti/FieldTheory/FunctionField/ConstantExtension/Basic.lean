/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.GeometricDegree
public import TauCeti.FieldTheory.FunctionField.ConstantField
public import Mathlib.FieldTheory.Normal.Basic

/-!
# Finite extensions of the constant field

A finite extension of constants yields a finite compositum over the original field, and a
separable extension of constants produces a separable compositum.  Exactness of the original
constant field is needed for neither.  The function-field theorem for arbitrary algebraic
extensions of constants is in `ConstantExtension.Algebraic`.

Under the hypotheses that make constant field extensions well behaved — the original constant
field `k` is exact in `F` and `k' / k` is separable — the compositum acquires no new separable
constants: no element of `F · k'` outside `k'` is separable over `k'`.  Comparing coordinates in
a basis of constants upgrades this to exactness of `k'` in `F · k'`
(`IsIntegrallyClosedIn.of_constantCompositum_eq_top` in `ConstantExtension.Basis`).
Separability of `k' / k` cannot simply be dropped: over an imperfect `k` an inseparable constant
field extension can enlarge the field of constants beyond `k'`.  For instance,
`k = 𝔽_p(t, u)` is exact in `F = k(x, y)` with `y ^ p = t * x ^ p + u`, but for `k' = k(t ^ (1/p))`
the element `y - t ^ (1/p) * x` of `F · k'` is a `p`-th root of `u`, and `u ^ (1/p) ∉ k'`.

Finite extensions of constants with as many elements as desired always exist, realized as
composita inside an algebraic closure of `F`.  Over a finite constant field this is how arguments
that need many constants, such as choosing a vector outside finitely many proper subspaces, are
carried out after a finite constant field extension.

## Main results

* `TauCeti.finiteDimensional_of_constantCompositum_eq_top`: a compositum with finite constants
  is finite over the original field.
* `TauCeti.finiteDimensional_base_of_constantCompositum_eq_top`: conversely, for an exact `k` and
  separable `k' / k`, a compositum finite over the original field has finite constants.
* `TauCeti.isSeparable_of_constantCompositum_eq_top`: the compositum of a separable constant
  field extension is separable over the original field.
* `TauCeti.separableClosure_eq_bot_of_constantCompositum_eq_top`: for a separable constant field
  extension of an exact constant field, `k'` is separably closed in `F · k'`.
* `TauCeti.adjoin_image_eq_top_of_constantCompositum_eq_top`: generators of `F` over `k` generate
  `F · k'` over `k'`.
* `TauCeti.isSeparable_adjoin_algebraMap_of_constantCompositum_eq_top`: if `F` is separable over
  `k(x)`, then `F · k'` is separable over `k'(x)`.
* `TauCeti.exists_finiteDimensional_lt_card_constantCompositum_eq_top` and
  `TauCeti.exists_finiteDimensional_normal_splits_constantCompositum_eq_top`: finite constant field
  extensions `F · k'` with more than a given number of constants, or with `k'` normal and
  splitting a given polynomial.

## Reference

H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.6,
Proposition 3.6.1.
-/

public section

open scoped IntermediateField

namespace TauCeti

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

/-- A compositum with finite constants is finite over the original field. The ambient field
`F'` is assumed to be precisely the compositum of `F` and `k'`. -/
theorem finiteDimensional_of_constantCompositum_eq_top [FiniteDimensional k k']
    (h : constantCompositum F k' F' = ⊤) : FiniteDimensional F F' := by
  let : Algebra.EssFiniteType k k' := inferInstance
  obtain ⟨S, hS⟩ := IntermediateField.fg_top k k'
  have htop : IntermediateField.adjoin F ((algebraMap k' F') '' (S : Set k')) = ⊤ := by
    rw [← constantCompositum_eq_adjoin_of_adjoin_eq_top (F := F) (k' := k')
      (F' := F') S hS]
    exact h
  have hfinite : Finite ((algebraMap k' F') '' (S : Set k')) :=
    S.finite_toSet.image _
  let : Finite ((algebraMap k' F') '' (S : Set k')) := hfinite
  have hi : ∀ x ∈ (algebraMap k' F') '' (S : Set k'), IsIntegral F x := by
    rintro x ⟨c, _, rfl⟩
    exact (IsIntegral.algebraMap (Algebra.IsIntegral.isIntegral (R := k) c)).tower_top
  have := IntermediateField.finiteDimensional_adjoin hi
  rw [htop] at this
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

/-- **Finiteness of the compositum detects finiteness of the constants**: if `k` is exact in `F`,
`k' / k` is separable and the compositum `F · k'` is finite over `F`, then `k' / k` is finite.  This
is the converse of `TauCeti.finiteDimensional_of_constantCompositum_eq_top`, by the degree identity
`[F · k' : F] = [k' : k]` of linear disjointness. -/
theorem finiteDimensional_base_of_constantCompositum_eq_top [FiniteDimensional F F']
    [Algebra.IsSeparable k k'] (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) : FiniteDimensional k k' := by
  have hrank := finrank_constantCompositum_eq_finrank_of_isSeparable F k' F' hex
  rw [h, IntermediateField.finrank_top'] at hrank
  exact Module.finite_of_finrank_pos (hrank ▸ Module.finrank_pos)

/-- A separable extension of the constant field produces a separable compositum over the
original field. -/
theorem isSeparable_of_constantCompositum_eq_top [Algebra.IsSeparable k k']
    (hcomp : constantCompositum F k' F' = ⊤) : Algebra.IsSeparable F F' := by
  rw [← IntermediateField.isSeparable_top]
  rw [← hcomp, constantCompositum_def,
    IntermediateField.isSeparable_adjoin_iff_isSeparable]
  rintro y ⟨c, rfl⟩
  exact IsSeparable.tower_top F <|
    (Algebra.IsSeparable.isSeparable k c).map (IsScalarTower.toAlgHom k k' F')
      (algebraMap k' F').injective

/-! ### The constant field of the compositum -/

/-- **The enlarged constant field is separably closed in the compositum**: if `k` is the exact
constant field of `F` and `k' / k` is separable algebraic, then every element of `F · k'` that is
separable over `k'` is already a constant of `k'`.

This is the separable half of Stichtenoth, Proposition 3.6.1(a);
`IsIntegrallyClosedIn.of_constantCompositum_eq_top` upgrades it to exactness of `k'`. -/
theorem separableClosure_eq_bot_of_constantCompositum_eq_top [Algebra.IsSeparable k k']
    (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤) :
    separableClosure k' F' = ⊥ := by
  refine eq_bot_iff.2 fun z hz ↦ IntermediateField.mem_bot.2 ?_
  refine mem_range_algebraMap_of_mem_adjoin_of_isSeparable_of_isIntegrallyClosedIn hex ?_
    (mem_separableClosure_iff.1 hz)
  rw [← constantCompositum_def, h]
  exact IntermediateField.mem_top

/-- **Generators of `F` generate the compositum over `k'`**: if a set `S` generates `F` over `k`,
then its image generates the compositum `F' = F · k'` over `k'`.  For instance, if
`F = k(x, y)` then `F · k' = k'(x, y)`. -/
theorem adjoin_image_eq_top_of_constantCompositum_eq_top {S : Set F}
    (hS : IntermediateField.adjoin k S = ⊤) (h : constantCompositum F k' F' = ⊤) :
    IntermediateField.adjoin k' (algebraMap F F' '' S) = ⊤ := by
  set E := IntermediateField.adjoin k' (algebraMap F F' '' S)
  -- `E` contains the image of `F = k(S)`, so it is an intermediate field of `F' / F`.
  have hFE : ∀ f : F, algebraMap F F' f ∈ E := by
    have hle : IntermediateField.adjoin k S ≤
        (E.restrictScalars k).comap (IsScalarTower.toAlgHom k F F') :=
      IntermediateField.adjoin_le_iff.mpr fun z hz ↦
        IntermediateField.subset_adjoin k' _ ⟨z, hz, rfl⟩
    exact fun f ↦ hle (hS ▸ IntermediateField.mem_top)
  have hle := (constantCompositum_le_iff F k' F'
    (K := E.toSubfield.toIntermediateField hFE)).mpr fun c ↦ E.algebraMap_mem c
  rw [h] at hle
  exact top_le_iff.mp fun z _ ↦ hle IntermediateField.mem_top

/-- **A separating element stays separating in the compositum**: if `F` is separable over `k(x)`,
then the compositum `F' = F · k'` is separable over `k'(x)`. No hypothesis on `k' / k` is needed,
since the new constants lie in `k'(x)`. -/
theorem isSeparable_adjoin_algebraMap_of_constantCompositum_eq_top
    (h : constantCompositum F k' F' = ⊤) {x : F} [Algebra.IsSeparable k⟮x⟯ F] :
    Algebra.IsSeparable k'⟮algebraMap F F' x⟯ F' := by
  set L := k'⟮algebraMap F F' x⟯
  -- `k(x)` maps into `k'(x)`.
  have hmem (a : k⟮x⟯) : algebraMap F F' a ∈ L := by
    have ha : algebraMap F F' a ∈ k⟮x⟯.map (IsScalarTower.toAlgHom k F F') := ⟨a, a.2, rfl⟩
    rw [IntermediateField.adjoin_map, Set.image_singleton] at ha
    exact (IntermediateField.adjoin_simple_le_iff.mpr
      (IntermediateField.mem_adjoin_simple_self k' (algebraMap F F' x)) :
        k⟮IsScalarTower.toAlgHom k F F' x⟯ ≤ L.restrictScalars k) ha
  let ψ : k⟮x⟯ →+* L :=
    ((algebraMap F F').comp (algebraMap k⟮x⟯ F)).codRestrict L.toSubfield hmem
  have hψ : (algebraMap L F').comp ψ = (algebraMap F F').comp (algebraMap k⟮x⟯ F) :=
    RingHom.ext fun a ↦ RingHom.codRestrict_apply _ _ hmem a
  -- Each element of `F` stays separable: its minimal polynomial over `k(x)`, mapped to `k'(x)`,
  -- is separable and vanishes at it.
  have hsep (z : F) : IsSeparable L (algebraMap F F' z) := by
    have hroot : Polynomial.aeval (algebraMap F F' z) ((minpoly k⟮x⟯ z).map ψ) = 0 := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_map, hψ,
        ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, minpoly.aeval, map_zero]
    have hp : (minpoly k⟮x⟯ z).Separable := Algebra.IsSeparable.isSeparable k⟮x⟯ z
    exact (hp.map (f := ψ)).of_dvd (minpoly.dvd L _ hroot)
  -- The image of `F` generates `F'` over `k'`, hence over `k'(x)`.
  have htop : IntermediateField.adjoin L (Set.range (algebraMap F F')) = ⊤ := by
    have hk' := adjoin_image_eq_top_of_constantCompositum_eq_top
      (IntermediateField.adjoin_univ k F) h
    rw [Set.image_univ] at hk'
    refine eq_top_iff.mpr fun w _ ↦ ?_
    exact (IntermediateField.adjoin_le_iff.mpr (IntermediateField.subset_adjoin L _) :
      IntermediateField.adjoin k' _ ≤ (IntermediateField.adjoin L _).restrictScalars k')
        (hk' ▸ IntermediateField.mem_top)
  rw [← IntermediateField.isSeparable_top, ← htop]
  exact (IntermediateField.isSeparable_adjoin_iff_isSeparable L F').mpr fun _ ⟨z, hz⟩ ↦ hz ▸ hsep z

/-! ### Large finite extensions of constants -/

variable (k F) in
/-- **Large finite constant field extensions exist**: for every `n`, there is a finite extension
`k' / k` with more than `n` elements together with a field `F'`, intermediate between `F` and its
algebraic closure, which is the compositum `F · k'`.  The elements of `k'` are chosen among the
infinitely many elements of the algebraic closure of `k` in that of `F`. -/
theorem exists_finiteDimensional_lt_card_constantCompositum_eq_top (n : ℕ) :
    ∃ (F' : IntermediateField F (AlgebraicClosure F)) (k' : IntermediateField k F'),
      FiniteDimensional k k' ∧ (n : ℕ∞) < ENat.card k' ∧ constantCompositum F k' F' = ⊤ := by
  classical
  let Ω := AlgebraicClosure F
  let A := algebraicClosure k Ω
  have : IsAlgClosed A := IsAlgClosure.isAlgClosed k
  obtain ⟨S, hS⟩ := Infinite.exists_subset_card_eq A (n + 1)
  -- adjoin the `n + 1` chosen algebraic constants `T` to `F`, and then to `k` inside `F(T)`
  let T : Set Ω := Subtype.val '' (S : Set A)
  let F' := IntermediateField.adjoin F T
  let T' : Set F' := Subtype.val ⁻¹' T
  have hT'T : Subtype.val '' T' = T :=
    Set.image_preimage_eq_of_subset fun x hx ↦ by
      simpa using IntermediateField.subset_adjoin F T hx
  have : Finite T' := (S.finite_toSet.image _).preimage Subtype.val_injective.injOn
  have hint : ∀ x ∈ T', IsIntegral k x := by
    rintro x ⟨a, -, hax⟩
    have hx : IsIntegral k (x : Ω) := by
      rw [← hax]
      exact (mem_algebraicClosure_iff.mp a.2).isIntegral
    exact (isIntegral_algHom_iff (F'.val.restrictScalars k) Subtype.val_injective).mp hx
  refine ⟨F', IntermediateField.adjoin k T', IntermediateField.finiteDimensional_adjoin hint,
    ?_, ?_⟩
  · have hT' : T'.encard = n + 1 := by
      rw [← Subtype.val_injective.injOn.encard_image, hT'T,
        Subtype.val_injective.injOn.encard_image, Set.encard_coe_eq_coe_finsetCard, hS]
      norm_cast
    have hle : T'.encard ≤ ENat.card (IntermediateField.adjoin k T') :=
      (Set.encard_le_encard (IntermediateField.subset_adjoin k T')).trans_eq
        (ENat.card_coe_set_eq _).symm
    rw [hT'] at hle
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self n) hle
  · have htop : IntermediateField.adjoin F T' = ⊤ := by
      apply IntermediateField.lift_injective
      rw [IntermediateField.lift_adjoin, hT'T, IntermediateField.lift_top]
    rw [eq_top_iff, ← htop, constantCompositum_def]
    refine IntermediateField.adjoin.mono _ _ _ fun x hx ↦ ?_
    exact ⟨⟨x, IntermediateField.subset_adjoin k T' hx⟩, rfl⟩

variable (F) in
/-- **A finite normal constant field extension splitting a polynomial exists**: for every
`f ∈ k[X]`, the splitting field `k'` of `f` over `k`, formed inside the algebraic closure of `F`, is
a finite normal extension of `k`, and `F' = F(roots of f)` is the compositum `F · k'`. -/
theorem exists_finiteDimensional_normal_splits_constantCompositum_eq_top (f : Polynomial k) :
    ∃ (F' : IntermediateField F (AlgebraicClosure F)) (k' : IntermediateField k F'),
      FiniteDimensional k k' ∧ Normal k k' ∧ (f.map (algebraMap k k')).Splits ∧
        Polynomial.IsSplittingField k k' f ∧ constantCompositum F k' F' = ⊤ := by
  let F' := IntermediateField.adjoin F ((f.map (algebraMap k F)).rootSet (AlgebraicClosure F))
  have : Polynomial.IsSplittingField F F' (f.map (algebraMap k F)) :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  have hsplit : (f.map (algebraMap k F')).Splits := by
    have := Polynomial.IsSplittingField.splits F' (f.map (algebraMap k F))
    rwa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at this
  let k' : IntermediateField k F' := IntermediateField.adjoin k (f.rootSet F')
  have : Polynomial.IsSplittingField k k' f :=
    IntermediateField.adjoin_rootSet_isSplittingField hsplit
  refine ⟨F', k', Polynomial.IsSplittingField.finiteDimensional k' f,
    Normal.of_isSplittingField f, Polynomial.IsSplittingField.splits k' f, this, ?_⟩
  -- Each root of `f` in the algebraic closure lies in `F'`, and there it lies in `k'`.
  refine eq_top_iff.mpr fun x _ ↦ ?_
  have hle : F' ≤ (constantCompositum F k' F').map F'.val := by
    refine IntermediateField.adjoin_le_iff.mpr fun r hr ↦ ?_
    have hrF' : r ∈ F' := IntermediateField.subset_adjoin _ _ hr
    have hroot : (⟨r, hrF'⟩ : F') ∈ f.rootSet F' := by
      rw [Polynomial.mem_rootSet] at hr ⊢
      refine ⟨fun hf ↦ hr.1 (by rw [hf, Polynomial.map_zero]), Subtype.ext ?_⟩
      rw [Polynomial.aeval_map_algebraMap] at hr
      have hval := Polynomial.aeval_algHom_apply (F'.val.restrictScalars k) (⟨r, hrF'⟩ : F') f
      simp only [AlgHom.coe_restrictScalars', IntermediateField.coe_val] at hval
      rw [← hval, ZeroMemClass.coe_zero]
      exact hr.2
    exact ⟨⟨r, hrF'⟩,
      algebraMap_mem_constantCompositum F k' F' ⟨_, IntermediateField.subset_adjoin k _ hroot⟩, rfl⟩
  -- The preimage `w` of `x` under the inclusion `F · k' → F'` is `x` itself.
  obtain ⟨w, hw, hwx⟩ := hle x.2
  obtain rfl : w = x := Subtype.ext hwx
  exact hw

end TauCeti
