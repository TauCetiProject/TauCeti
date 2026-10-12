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

end Place

end TauCeti
