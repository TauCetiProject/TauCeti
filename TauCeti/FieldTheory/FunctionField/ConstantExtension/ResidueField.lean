/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Algebraic
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.IntegralBasis
public import TauCeti.FieldTheory.FunctionField.Place.Degree
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Fibre

/-!
# Residue fields in a constant field extension

Let `F' = F · k'` be a finite separable constant field extension of an algebraic function field
`F / k` with exact constant field `k`, and let `P'` be a place of `F' / k'` lying over the place
`P` of `F / k`.  The residue field of `P'` is the compositum of the residue field of `P` and the
new constants:

`F'_{P'} = F_P · k'`.

In fact more is true: `F'_{P'}` is spanned as an `F_P`-vector space by the image of `k'`.  Every
residue class at `P'` is represented by a function regular at all the places over `P`, hence
integral over `𝒪_P`, and such a function is an `𝒪_P`-combination of a `k`-basis of `k'`
(`TauCeti.Place.isIntegralBasis_constantBasis`).  Reducing that combination at `P'` writes the
residue class as an `F_P`-combination of residues of constants.

Consequently a place becomes rational as soon as the constants are enlarged enough: if `k' / k`
is normal and the residue field `F_P` admits a `k`-embedding into `k'`, every place of `F'` over
`P` has degree one.  Each element of `F_P` is a root of its minimal polynomial over `k`, which
splits in `k'`, so its residue in `F'_{P'}` is already a constant.

## Main results

* `TauCeti.Place.span_range_algebraMap_residueField_eq_top_of_constantCompositum_eq_top`:
  `F'_{P'}` is spanned over `F_P` by the image of `k'`.
* `TauCeti.Place.adjoin_range_algebraMap_residueField_eq_top_of_constantCompositum_eq_top`:
  **`F'_{P'} = F_P · k'`** (Stichtenoth, Theorem 3.6.3(g)).
* `TauCeti.Place.degree_eq_one_of_constantCompositum_eq_top`: a place over `P` is rational when
  `k' / k` is normal and `F_P` embeds into `k'` over `k`.
* `TauCeti.Place.exists_constantCompositum_eq_top_and_forall_degree_eq_one`: a place with
  separable residue field becomes rational after a finite separable extension of constants.
* `TauCeti.Place.exists_ord_sub_algebraMap_eq_one_of_ord_aeval_eq_one`: at a rational place `P'`
  unramified over `P`, a prime element `q(z)` of `P` with `q` separable yields a prime element
  `z - a` of `P'`.

## Reference

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 3.6.3(g).
-/

public section

open Module

namespace TauCeti

namespace Place

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']
variable [FiniteDimensional k k'] [Algebra.IsSeparable k k']

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

/-- **The residue field of a constant field extension is spanned by the constants**: for a finite
separable constant field extension `F' = F · k'` of `F / k` with exact constant field `k`, the
residue field of a place `P'` of `F' / k'` is spanned over the residue field of the place below by
the image of `k'`. -/
theorem span_range_algebraMap_residueField_eq_top_of_constantCompositum_eq_top
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) (P' : Place k' F') :
    letI := finiteDimensional_of_constantCompositum_eq_top (k := k) (k' := k') h
    Submodule.span (P'.restrict k F).ResidueField (Set.range (algebraMap k' P'.ResidueField)) =
      ⊤ := by
  let := finiteDimensional_of_constantCompositum_eq_top (k := k) (k' := k') h
  set P := P'.restrict k F
  refine eq_top_iff.2 fun y _ ↦ ?_
  -- Represent `y` by a function regular at every place over `P`, hence integral over `𝒪_P`.
  classical
  obtain ⟨g, hg, hgy⟩ := exists_forall_residue_eq
    (P := fun Q : {Q : Place k' F' // Q.restrict k F = P} ↦ (Q : Place k' F'))
    Subtype.val_injective fun Q ↦ if hQ : (Q : Place k' F') = P' then hQ ▸ y else 0
  have hint : IsIntegral P.integers g :=
    (isIntegral_iff_forall_restrict_eq_mem_integers (hF.of_constantCompositum_eq_top h) P).2
      fun Q hQ ↦ hg ⟨Q, hQ⟩
  -- Expand `g` in a basis of constants, with coordinates in `𝒪_P`.
  let b := Module.finBasis k k'
  have hb := isIntegralBasis_constantBasis hex h b P
  have hrepr := hb.isIntegral_iff_repr_mem.1 hint
  set a : Fin (finrank k k') → P.integers := fun i ↦ ⟨(constantBasis hex h b).repr g i, hrepr i⟩
  have hgsum : (⟨g, hg ⟨P', rfl⟩⟩ : P'.integers) =
      ∑ i, algebraMap P.integers P'.integers (a i) * algebraMap k' P'.integers (b i) := by
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, coe_algebraMap_constants, a]
    conv_lhs => rw [← (constantBasis hex h b).sum_repr g]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [coe_algebraMap_integers, constantBasis_apply, Algebra.smul_def]
  have hy : y = IsLocalRing.residue P'.integers ⟨g, hg ⟨P', rfl⟩⟩ := by
    simpa using (hgy ⟨P', rfl⟩).symm
  rw [hy, hgsum, map_sum]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  rw [map_mul, ← IsLocalRing.ResidueField.algebraMap_residue, ← algebraMap_residueField (R := k'),
    ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _))

/-- **The residue field of a constant field extension is a compositum** (Stichtenoth,
Theorem 3.6.3(g)): for a finite separable constant field extension `F' = F · k'` of `F / k` with
exact constant field `k`, the residue field of a place `P'` of `F' / k'` is generated over the
residue field `F_P` of the place below by the constants: `F'_{P'} = F_P · k'`. -/
theorem adjoin_range_algebraMap_residueField_eq_top_of_constantCompositum_eq_top
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) (P' : Place k' F') :
    letI := finiteDimensional_of_constantCompositum_eq_top (k := k) (k' := k') h
    IntermediateField.adjoin (P'.restrict k F).ResidueField
      (Set.range (algebraMap k' P'.ResidueField)) = ⊤ := by
  let := finiteDimensional_of_constantCompositum_eq_top (k := k) (k' := k') h
  -- The adjoined field contains the span, which is already everything.
  refine eq_top_iff.2 fun y _ ↦
    (Submodule.span_le (p := (IntermediateField.adjoin _ _).toSubalgebra.toSubmodule)).2
      (IntermediateField.subset_adjoin _ _) ?_
  rw [span_range_algebraMap_residueField_eq_top_of_constantCompositum_eq_top hF hex h P']
  exact Submodule.mem_top

/-- **A place becomes rational in a large enough normal constant field extension**: for a finite
separable normal constant field extension `F' = F · k'` of `F / k` with exact constant field `k`,
a place `P'` of `F' / k'` has degree one as soon as the residue field of the place below admits a
`k`-embedding into `k'`. -/
theorem degree_eq_one_of_constantCompositum_eq_top [Normal k k'] (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤) (P' : Place k' F')
    (φ : letI := finiteDimensional_of_constantCompositum_eq_top (k := k) (k' := k') h
      (P'.restrict k F).ResidueField →ₐ[k] k') :
    P'.degree = 1 := by
  let := finiteDimensional_of_constantCompositum_eq_top (k := k) (k' := k') h
  set P := P'.restrict k F
  let ι := algebraMap k' P'.ResidueField
  -- The two routes from `k` into `F'_{P'}`, through `F_P` and through `k'`, agree.
  have hcomp (c : k) : algebraMap P.ResidueField P'.ResidueField (algebraMap k P.ResidueField c) =
      ι (algebraMap k k' c) := by
    rw [algebraMap_residueField (R := k), IsLocalRing.ResidueField.algebraMap_residue,
      algebraMap_residueField (R := k')]
    congr 1
    apply Subtype.ext
    rw [coe_algebraMap_integers, coe_algebraMap_constants, coe_algebraMap_constants,
      ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  -- Each element of `F_P` reduces to a constant, as a root of a polynomial splitting in `k'`.
  have hmem (α : P.ResidueField) : algebraMap P.ResidueField P'.ResidueField α ∈ ι.range := by
    have := P.finiteDimensional_residueField hF
    have hαint : IsIntegral k α := Algebra.IsIntegral.isIntegral α
    have hsplit := Normal.splits (F := k) (K := k') inferInstance (φ α)
    rw [minpoly.algHom_eq φ φ.injective α] at hsplit
    refine hsplit.mem_range_of_isRoot (Polynomial.map_ne_zero (minpoly.ne_zero hαint)) ?_
    have hroot : ((minpoly k α).map (algebraMap k P.ResidueField)).IsRoot α := by
      rw [Polynomial.IsRoot, Polynomial.eval_map_algebraMap, minpoly.aeval]
    rw [Polynomial.map_map, show ι.comp (algebraMap k k') =
        (algebraMap P.ResidueField P'.ResidueField).comp (algebraMap k P.ResidueField) from
        RingHom.ext fun c ↦ (hcomp c).symm, ← Polynomial.map_map]
    exact hroot.map
  rw [degree_eq_one_iff_algebraMap_surjective]
  intro y
  have hy : y ∈ Submodule.span P.ResidueField (Set.range ι) := by
    rw [span_range_algebraMap_residueField_eq_top_of_constantCompositum_eq_top hF hex h P']
    exact Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, map_zero ι⟩
  | add x y _ _ hx hy => exact ι.range.add_mem hx hy
  | smul r x _ hx => exact Algebra.smul_def r x ▸ ι.range.mul_mem (hmem r) hx

omit [Field k'] [Field F'] [Algebra k k'] [Algebra k F'] [Algebra k' F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F'] [FiniteDimensional k k']
  [Algebra.IsSeparable k k'] in
/-- **A place becomes rational after a finite separable extension of constants**: if the residue
field of a place `P` of `F / k`, with `k` exact, is separable over `k`, then some finite separable
constant field extension `F' = F · k'`, formed inside an algebraic closure of `F`, has only places
of degree one over `P`.

The constants `k'` are the splitting field of the minimal polynomial of a primitive element of
`F_P / k`, which is normal over `k` and receives `F_P`. -/
theorem exists_constantCompositum_eq_top_and_forall_degree_eq_one (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (P : Place k F) [Algebra.IsSeparable k P.ResidueField] :
    ∃ (F' : IntermediateField F (AlgebraicClosure F)) (k' : IntermediateField k F'),
      FiniteDimensional k k' ∧ Algebra.IsSeparable k k' ∧ constantCompositum F k' F' = ⊤ ∧
        ∀ P' : Place k' F', P'.restrict k F = P → P'.degree = 1 := by
  classical
  have := P.finiteDimensional_residueField hF
  -- Adjoin to `F` the roots of the minimal polynomial `p` of a primitive element `γ` of `F_P`.
  obtain ⟨γ, hγ⟩ := Field.exists_primitive_element k P.ResidueField
  have hγint : IsIntegral k γ := Algebra.IsIntegral.isIntegral γ
  set p := minpoly k γ
  let Ω := AlgebraicClosure F
  let F' := IntermediateField.adjoin F (p.rootSet Ω)
  have hsplit : (p.map (algebraMap k F')).Splits :=
    IntermediateField.splits_of_splits (F := F'.restrictScalars k)
      (IsAlgClosed.splits (p.map (algebraMap k Ω))) fun z hz ↦
        IntermediateField.subset_adjoin F (p.rootSet Ω) hz
  let k' := IntermediateField.adjoin k (p.rootSet F')
  have : p.IsSplittingField k k' := IntermediateField.adjoin_rootSet_isSplittingField hsplit
  have : FiniteDimensional k k' := Polynomial.IsSplittingField.finiteDimensional k' p
  have : Normal k k' := Normal.of_isSplittingField p
  have : Algebra.IsSeparable k k' :=
    Algebra.isSeparable_of_separable_splitting_field (F := k) (E := k')
      (Algebra.IsSeparable.isSeparable k γ)
  -- `F'` is generated over `F` by the roots of `p`, which lie in `k'`.
  have htop : constantCompositum F k' F' = ⊤ := by
    have : IsScalarTower k F' Ω := .of_algebraMap_eq fun c ↦ IsScalarTower.algebraMap_apply k F Ω c
    have himage : Subtype.val '' p.rootSet F' = p.rootSet Ω := hsplit.image_rootSet_algebraMap
    have hF' : IntermediateField.adjoin F (p.rootSet F') = ⊤ := by
      apply IntermediateField.lift_injective
      rw [IntermediateField.lift_adjoin, himage, IntermediateField.lift_top]
    rw [eq_top_iff, ← hF', constantCompositum_def]
    exact IntermediateField.adjoin.mono _ _ _ fun z hz ↦
      ⟨⟨z, IntermediateField.subset_adjoin k _ hz⟩, rfl⟩
  -- `F_P = k(γ)` embeds into `k'`, where `p` has a root.
  obtain ⟨r, hr⟩ := (Polynomial.IsSplittingField.splits k' p).exists_eval_eq_zero (by
    rw [Polynomial.degree_map]; exact (minpoly.degree_pos hγint).ne')
  have hroot : r ∈ p.aroots k' := by
    rw [Polynomial.mem_aroots]
    exact ⟨minpoly.ne_zero hγint, by rwa [Polynomial.eval_map_algebraMap] at hr⟩
  let φ : P.ResidueField →ₐ[k] k' := ((IntermediateField.algHomAdjoinIntegralEquiv k hγint).symm
    ⟨r, hroot⟩).comp ((IntermediateField.equivOfEq hγ).trans IntermediateField.topEquiv).symm
  refine ⟨F', k', inferInstance, inferInstance, htop, fun P' hP' ↦ ?_⟩
  exact degree_eq_one_of_constantCompositum_eq_top hF hex htop P' (hP' ▸ φ)

/-! ### Prime elements at a rational place above -/

open _root_.Polynomial in
omit [FiniteDimensional k k'] [Algebra.IsSeparable k k'] in
/-- **A prime element `q(z)` below gives a prime element `z - a` at a rational place above**: at a
rational place `P'` of `F'` over a place `P` of `F` with `e(P' ∣ P) = 1`, a prime element `q(z)` of
`P`, with `q` separable over `k` and `z` regular at `P`, gives a prime element `z - a` of `P'` for
some constant `a`, namely the value of `z` at `P'`, which is a simple root of `q`. -/
theorem exists_ord_sub_algebraMap_eq_one_of_ord_aeval_eq_one [Algebra.IsIntegral F F']
    {P' : Place k' F'} (hdeg : P'.degree = 1) (he : P'.ramificationIdx F = 1) {z : F}
    (hz : 0 ≤ (P'.restrict k F).ord z) {q : Polynomial k} (hq : q.Separable)
    (hqz : (P'.restrict k F).ord (Polynomial.aeval z q) = 1) :
    ∃ a : k', P'.ord (algebraMap F F' z - algebraMap k' F' a) = 1 := by
  set z' := algebraMap F F' z
  have hzint : z' ∈ P'.integers := (mem_integers_restrict_iff k F P' z).mp
    ((P'.restrict k F).mem_integers_iff_ord_nonneg.mpr hz)
  obtain ⟨a, ha⟩ := (degree_eq_one_iff_forall_exists_valuation_sub_lt_one P').mp hdeg z' hzint
  refine ⟨a, ?_⟩
  -- `Q(z')`, with `Q` the image of `q` over `k'`, is a prime element of `P'`.
  set Q := q.map (algebraMap k k')
  have hQz : P'.ord (aeval z' Q) = 1 := by
    rw [aeval_map_algebraMap, aeval_algebraMap_apply, ord_algebraMap_restrict k F P', he, hqz]
    simp
  have hord_eq_zero {w : F'} (hw : P'.valuation w = 1) : P'.ord w = 0 := by
    rw [ord_def, hw, WithZero.log_one, neg_zero]
  -- `a` is a root of `Q`, simple because `Q` is separable, so `Q = (X - a) R` with `R(a) ≠ 0`.
  have hQa : Q.eval a = 0 := by
    by_contra hne
    rw [hord_eq_zero (valuation_aeval_eq_one_of_valuation_sub_lt_one ha hne)] at hQz
    exact zero_ne_one hQz
  set R := Q /ₘ (X - C a)
  have hQR : (X - C a) * R = Q := mul_divByMonic_eq_iff_isRoot.mpr hQa
  have hRa : R.eval a ≠ 0 := by
    have hsep : Q.Separable := hq.map
    have hder := hsep.aeval_derivative_ne_zero (x := a) (by rwa [coe_aeval_eq_eval])
    rw [coe_aeval_eq_eval] at hder
    rw [← hQR] at hder
    simpa using hder
  -- So `ord (z' - a) = ord Q(z') - ord R(z') = 1 - 0`.
  have hRz := hord_eq_zero (valuation_aeval_eq_one_of_valuation_sub_lt_one ha hRa)
  have hfac : aeval z' Q = (z' - algebraMap k' F' a) * aeval z' R := by
    rw [← hQR, map_mul, map_sub, aeval_X, aeval_C]
  have hne : aeval z' Q ≠ 0 := fun h0 ↦ by rw [h0, ord_zero] at hQz; exact zero_ne_one hQz
  rw [hfac] at hQz hne
  rw [P'.ord_mul (left_ne_zero_of_mul hne) (right_ne_zero_of_mul hne), hRz, add_zero] at hQz
  exact hQz

end Place

end TauCeti
