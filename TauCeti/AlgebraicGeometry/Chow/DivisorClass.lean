/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Chow.Basic
public import TauCeti.AlgebraicGeometry.Scheme.LocalDimension
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Principal
import TauCeti.AlgebraicGeometry.Morphisms.ClosedImmersion.Basic
import TauCeti.AlgebraicGeometry.Scheme.GenericPoint

/-!
# The divisor class comparison: `Cl(X) ≃ CH_{n-1}(X)`

Let `X` be an irreducible scheme locally of finite type over a field `κ`, of dimension `n`. By the
dimension formula `codim x + dim {x}⁻ = n`
(`TauCeti.AlgebraicGeometry.coheight_add_height_eq_topologicalKrullDim`), the points of
codimension one of `X` are exactly its points of dimension `n - 1`
(`Chow.coheight_eq_one_iff_mem_pointsOfDimension`), and the generic point is its only point of
dimension `n` (`Chow.mem_pointsOfDimension_iff_eq_genericPoint`). If `X` is quasi-compact, every
cycle has finite support. Hence:

* `Chow.cyclesOfDimension_eq_finiteCodimensionOneCycles`: the `(n - 1)`-cycles are the finite
  cycles supported in codimension one;
* `Chow.weilDivisorEquivCyclesOfDimension`: the Weil divisors of `X` are additively equivalent to
  the `(n - 1)`-cycles `Z_{n-1}(X)`, by extension by zero away from codimension one
  (`SchemeWeilDivisor.toAlgebraicCycle`).

If `X` is moreover integral and Noetherian, rational equivalence of `(n - 1)`-cycles is linear
equivalence of Weil divisors:

* `Chow.weilDivisorEquivCyclesOfDimension_principalDivisor_mem_ratEquiv`: a principal Weil divisor
  is rationally equivalent to zero, being the principal cycle `div r` of `X` itself;
* `Chow.isIso_of_genericPoint_mem_pointsOfDimension`: conversely, an integral closed subscheme of
  dimension `n` of `X` is `X` itself, so a rational equivalence on `X` in dimension `n - 1` is a
  finite sum of principal cycles of `X` (orders of vanishing are invariant under isomorphisms,
  `AlgebraicCycle.map_height_div_of_isIso`);
* `Chow.classGroupEquivChowGroup`: the **divisor class comparison**, an isomorphism from the divisor
  class group `Cl(X)` (Weil divisors modulo principal divisors) to the Chow group `CH_{n-1}(X)`,
  sending the class of a Weil divisor to the class of its `(n - 1)`-cycle
  (`Chow.classGroupEquivChowGroup_divisorClass`, `Chow.classGroupEquivChowGroup_symm_cycleClass`).

No separation or normality is assumed. This is the identification of `CH_{n-1}(X)` with the Weil
divisor class group in Fulton, *Intersection Theory*, §1.3 and §2.1; see also
[Stacks, Section 42.24](https://stacks.math.columbia.edu/tag/02SI).
-/

public section

open AlgebraicGeometry Order CategoryTheory

universe u

namespace TauCeti.AlgebraicGeometry.Chow

variable (κ : Type u) [Field κ] {X : Scheme.{u}} [X.Over (Spec (.of κ))]
  [LocallyOfFiniteType (X ↘ Spec (.of κ))]

section Dimension

variable [IrreducibleSpace X] {n : ℕ}

include κ in
/-- On an irreducible scheme of dimension `n` locally of finite type over a field, every point
has finite codimension `c` and finite closure dimension `d` with `c + d = n`. -/
private lemma exists_coheight_height (hn : topologicalKrullDim X = n) (x : X) :
    ∃ c d : ℕ, coheight x = c ∧ height x = d ∧ c + d = n := by
  have h' := coheight_add_height_eq_topologicalKrullDim κ x
  rw [hn] at h'
  have h : coheight x + height x = n := by exact_mod_cast h'
  have hc : coheight x ≠ ⊤ := fun hc ↦ by simp [hc] at h
  have hd : height x ≠ ⊤ := fun hd ↦ by simp [hd] at h
  lift coheight x to ℕ using hc with c hc
  lift height x to ℕ using hd with d hd
  exact ⟨c, d, rfl, rfl, by exact_mod_cast h⟩

include κ in
/-- On an irreducible scheme of dimension `n` locally of finite type over a field, the points of
codimension one are exactly the points of dimension `n - 1`. -/
lemma coheight_eq_one_iff_mem_pointsOfDimension (hn : topologicalKrullDim X = n) {x : X} :
    coheight x = 1 ↔ x ∈ pointsOfDimension X (n - 1) := by
  obtain ⟨c, d, hc, hd, hcd⟩ := exists_coheight_height κ hn x
  simp only [hc, hd, mem_pointsOfDimension, Nat.cast_inj, exists_eq_left', Nat.cast_eq_one]
  omega

include κ in
/-- On an irreducible scheme of dimension `n` locally of finite type over a field, the generic
point is the only point of dimension `n`. -/
lemma mem_pointsOfDimension_iff_eq_genericPoint (hn : topologicalKrullDim X = n) {x : X} :
    x ∈ pointsOfDimension X n ↔ x = genericPoint X := by
  obtain ⟨c, d, hc, hd, hcd⟩ := exists_coheight_height κ hn x
  rw [← TauCeti.AlgebraicGeometry.Scheme.isMax_iff_eq_genericPoint, ← coheight_eq_zero, hc,
    Nat.cast_eq_zero]
  simp only [hd, mem_pointsOfDimension, Nat.cast_inj, exists_eq_left']
  omega

variable [CompactSpace X]

include κ in
/-- On a quasi-compact irreducible scheme of dimension `n` locally of finite type over a field, the
`(n - 1)`-cycles are exactly the finite cycles supported in codimension one; the finiteness is
automatic since the scheme is quasi-compact. -/
lemma cyclesOfDimension_eq_finiteCodimensionOneCycles (hn : topologicalKrullDim X = n) :
    cyclesOfDimension X (n - 1) = SchemeWeilDivisor.finiteCodimensionOneCycles X := by
  ext α
  rw [mem_cyclesOfDimension_iff, SchemeWeilDivisor.mem_finiteCodimensionOneCycles_iff]
  exact ⟨fun h ↦ ⟨Function.locallyFinsupp.finite_support α,
      AlgebraicCycle.isWeilDivisor_iff.mpr fun x hx ↦
        (coheight_eq_one_iff_mem_pointsOfDimension κ hn).mpr (h hx)⟩,
    fun h x hx ↦ (coheight_eq_one_iff_mem_pointsOfDimension κ hn).mp (h.2.coheight_eq_one hx)⟩

/-- On a quasi-compact irreducible scheme of dimension `n` locally of finite type over a field `κ`,
the Weil divisors are additively equivalent to the `(n - 1)`-cycles, by extension by zero away from
codimension one. -/
noncomputable def weilDivisorEquivCyclesOfDimension (hn : topologicalKrullDim X = n) :
    SchemeWeilDivisor X ≃+ cyclesOfDimension X (n - 1) :=
  SchemeWeilDivisor.equivFiniteCodimensionOneCycles.trans
    (AddEquiv.addSubgroupCongr (cyclesOfDimension_eq_finiteCodimensionOneCycles κ hn).symm)

/-- The `(n - 1)`-cycle of a Weil divisor is its extension by zero away from codimension one. -/
@[simp]
lemma coe_weilDivisorEquivCyclesOfDimension_apply (hn : topologicalKrullDim X = n)
    (D : SchemeWeilDivisor X) :
    (weilDivisorEquivCyclesOfDimension κ hn D : AlgebraicCycle X ℤ) =
      SchemeWeilDivisor.toAlgebraicCycle D :=
  SchemeWeilDivisor.coe_equivFiniteCodimensionOneCycles_apply D

/-- The Weil divisor of an `(n - 1)`-cycle has, at each codimension-one point, the coefficient of
the cycle. -/
@[simp]
lemma weilDivisorEquivCyclesOfDimension_symm_apply_apply (hn : topologicalKrullDim X = n)
    (α : cyclesOfDimension X (n - 1)) (x : CodimensionOnePoint X) :
    (weilDivisorEquivCyclesOfDimension κ hn).symm α x = (α : AlgebraicCycle X ℤ) x :=
  SchemeWeilDivisor.equivFiniteCodimensionOneCycles_symm_apply_apply _ x

end Dimension

section ClassGroup

variable [IsIntegral X] [IsNoetherian X] {n : ℕ}

/-- The `(n - 1)`-cycle of a principal Weil divisor `div r` is rationally equivalent to zero: it is
the principal cycle of `r` on the integral closed subscheme `X` of dimension `n`. -/
lemma weilDivisorEquivCyclesOfDimension_principalDivisor_mem_ratEquiv
    (hn : topologicalKrullDim X = n) (r : X.functionFieldˣ) :
    weilDivisorEquivCyclesOfDimension κ hn
        ((WeilDivisor.OrderSystem.ofScheme X).principalDivisor (Additive.ofMul r)) ∈
      RatEquiv X (n - 1) := by
  refine mem_ratEquiv_of_coe_eq_map_div (𝟙 X) ?_ r ?_
  · rw [sub_add_cancel, mem_pointsOfDimension_iff_eq_genericPoint κ hn]
  · rw [coe_weilDivisorEquivCyclesOfDimension_apply,
      AlgebraicCycle.toAlgebraicCycle_principalDivisor, AlgebraicCycle.map_id]

omit [AlgebraicGeometry.IsNoetherian X] in
include κ in
/-- An integral closed subscheme of dimension `n` of an integral scheme `X` of dimension `n` locally
of finite type over a field is all of `X`: the closed immersion is an isomorphism. Its image is a
closed set containing the generic point of `X`. -/
lemma isIso_of_genericPoint_mem_pointsOfDimension (hn : topologicalKrullDim X = n)
    {W : Scheme.{u}} [IsIntegral W] (i : W ⟶ X) [IsClosedImmersion i]
    (hW : genericPoint W ∈ pointsOfDimension W n) : IsIso i := by
  have hi : i (genericPoint W) = genericPoint X := by
    rw [← mem_pointsOfDimension_iff_eq_genericPoint κ hn, mem_pointsOfDimension,
      Scheme.Hom.height_apply_eq_height]
    exact mem_pointsOfDimension.mp hW
  have : Surjective i := ⟨fun x ↦
    (genericPoint_specializes x).mem_closed i.isClosedEmbedding.isClosed_range ⟨_, hi⟩⟩
  exact isIso_of_isClosedImmersion_of_surjective i

/-- The map from the divisor class group `Cl(X)` to the Chow group `CH_{n-1}(X)`, sending the class
of a Weil divisor to the class of its `(n - 1)`-cycle. -/
private noncomputable def classGroupToChowGroup (hn : topologicalKrullDim X = n) :
    (WeilDivisor.OrderSystem.ofScheme X).ClassGroup →+ ChowGroup X (n - 1) :=
  WeilDivisor.OrderSystem.ClassGroup.lift _
    (cycleClass.comp (weilDivisorEquivCyclesOfDimension κ hn).toAddMonoidHom) fun g ↦
      cycleClass_eq_zero_iff.mpr <|
        weilDivisorEquivCyclesOfDimension_principalDivisor_mem_ratEquiv κ hn (Additive.toMul g)

/-- The map `Cl(X) →+ CH_{n-1}(X)` on divisor classes. -/
private lemma classGroupToChowGroup_divisorClass (hn : topologicalKrullDim X = n)
    (D : SchemeWeilDivisor X) :
    classGroupToChowGroup κ hn ((WeilDivisor.OrderSystem.ofScheme X).divisorClass D) =
      cycleClass (weilDivisorEquivCyclesOfDimension κ hn D) :=
  WeilDivisor.OrderSystem.ClassGroup.lift_divisorClass _ _ _ D

/-- Every class in `CH_{n-1}(X)` is the class of a Weil divisor. -/
private lemma classGroupToChowGroup_surjective (hn : topologicalKrullDim X = n) :
    Function.Surjective (classGroupToChowGroup κ hn) := by
  intro a
  obtain ⟨α, rfl⟩ := cycleClass_surjective a
  refine ⟨(WeilDivisor.OrderSystem.ofScheme X).divisorClass
    ((weilDivisorEquivCyclesOfDimension κ hn).symm α), ?_⟩
  rw [classGroupToChowGroup_divisorClass, AddEquiv.apply_symm_apply]

/-- A Weil divisor whose `(n - 1)`-cycle is rationally equivalent to zero is principal. The
subschemes of a rational equivalence are integral of dimension `n`, hence isomorphic to `X`; there
are finitely many of them, since they all contain the generic point; and the pushforward of a
principal cycle along an isomorphism is principal. -/
private lemma classGroupToChowGroup_injective (hn : topologicalKrullDim X = n) :
    Function.Injective (classGroupToChowGroup κ hn) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨D, rfl⟩ := (WeilDivisor.OrderSystem.ofScheme X).divisorClass_surjective c
  rw [classGroupToChowGroup_divisorClass, cycleClass_eq_zero_iff] at hc
  obtain ⟨F, hF⟩ := mem_ratEquiv_iff.mp hc
  rw [WeilDivisor.OrderSystem.divisorClass_eq_zero_iff]
  have hiso (j : F.ι) : IsIso (F.i j) :=
    isIso_of_genericPoint_mem_pointsOfDimension κ hn (F.i j) (by
      simpa using F.genericPoint_mem j)
  -- The family is finite: every member contains the generic point of `X`.
  have : Finite F.ι := by
    obtain ⟨t, ht, hfin⟩ := F.locallyFinite (genericPoint X)
    refine Set.finite_univ_iff.mp (hfin.subset fun j _ ↦ ?_)
    have := hiso j
    exact ⟨genericPoint X, (F.i j).surjective _, mem_of_mem_nhds ht⟩
  let := Fintype.ofFinite F.ι
  -- The `j`-th member contributes the principal cycle of the transported function `g j`.
  let g (j : F.ι) : X.functionFieldˣ :=
    Units.map (inv (F.i j)).functionFieldMap.hom.toMonoidHom (F.r j)
  have hcomp (j : F.ι) : F.component j = AlgebraicCycle.div (g j) := by
    have := hiso j
    rw [RatEquivFamily.component_def, AlgebraicCycle.map_height_div_of_isIso]
  refine (WeilDivisor.OrderSystem.ofScheme X).mem_principalSubgroup.mpr
    ⟨∑ j, Additive.ofMul (g j), SchemeWeilDivisor.toAlgebraicCycle_injective ?_⟩
  rw [← WeilDivisor.OrderSystem.principalHom_apply, map_sum, map_sum,
    ← coe_weilDivisorEquivCyclesOfDimension_apply κ hn, ← hF]
  ext x
  simp only [WeilDivisor.OrderSystem.principalHom_apply,
    AlgebraicCycle.toAlgebraicCycle_principalDivisor,
    Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply, RatEquivFamily.cycle_apply,
    finsum_eq_sum_of_fintype, hcomp]

/-- **The divisor class comparison.** For an integral Noetherian scheme `X` of dimension `n`
locally of finite type over a field `κ`, the divisor class group `Cl(X)` (Weil divisors modulo
principal divisors) is isomorphic to the Chow group `CH_{n-1}(X)`, by sending the class of a Weil
divisor to the class of its `(n - 1)`-cycle. -/
noncomputable def classGroupEquivChowGroup (hn : topologicalKrullDim X = n) :
    (WeilDivisor.OrderSystem.ofScheme X).ClassGroup ≃+ ChowGroup X (n - 1) :=
  AddEquiv.ofBijective (classGroupToChowGroup κ hn)
    ⟨classGroupToChowGroup_injective κ hn, classGroupToChowGroup_surjective κ hn⟩

/-- The divisor class comparison sends the class of a Weil divisor to the class of its
`(n - 1)`-cycle. -/
@[simp]
lemma classGroupEquivChowGroup_divisorClass (hn : topologicalKrullDim X = n)
    (D : SchemeWeilDivisor X) :
    classGroupEquivChowGroup κ hn ((WeilDivisor.OrderSystem.ofScheme X).divisorClass D) =
      cycleClass (weilDivisorEquivCyclesOfDimension κ hn D) :=
  classGroupToChowGroup_divisorClass κ hn D

/-- The inverse of the divisor class comparison sends the class of an `(n - 1)`-cycle to the class
of its Weil divisor. -/
@[simp]
lemma classGroupEquivChowGroup_symm_cycleClass (hn : topologicalKrullDim X = n)
    (α : cyclesOfDimension X (n - 1)) :
    (classGroupEquivChowGroup κ hn).symm (cycleClass α) =
      (WeilDivisor.OrderSystem.ofScheme X).divisorClass
        ((weilDivisorEquivCyclesOfDimension κ hn).symm α) := by
  rw [AddEquiv.symm_apply_eq, classGroupEquivChowGroup_divisorClass, AddEquiv.apply_symm_apply]

end ClassGroup

end TauCeti.AlgebraicGeometry.Chow
