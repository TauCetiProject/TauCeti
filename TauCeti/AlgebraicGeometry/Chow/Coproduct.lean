/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Chow.ClosedImmersion
public import TauCeti.AlgebraicGeometry.Limits.Coproduct
import TauCeti.AlgebraicGeometry.Morphisms.ClosedImmersion.Basic
import TauCeti.Topology.LocallyFinite.Sigma
import TauCeti.Topology.LocallyFinsupp.Comap

/-!
# Cycles and Chow groups of a coproduct of schemes

Let `X : I → Scheme` be a family of schemes indexed by a type in the universe of the schemes. Each
summand `X i` is open and closed in `∐ X`, so the closure of a point of `X i` is the same in `X i`
and in `∐ X`. Hence a `k`-cycle on `∐ X` is the same thing as a family of `k`-cycles on the `X i`,
possibly with infinitely many nonzero members:

* `Chow.cyclesSigmaEquiv X k : Z_k(∐ X) ≃+ ∏ i, Z_k(X i)` restricts a cycle to every summand
  (`Chow.cyclesSigmaEquiv_apply`); its inverse places the cycle `γ i` on the summand `X i`
  (`Chow.cyclesSigmaEquiv_symm_apply`).

An integral closed subscheme of `∐ X` is irreducible, so it lies in a single summand. Therefore a
locally finite family of integral closed subschemes with rational functions on `∐ X` splits into
such families on the summands, and conversely such families on the summands glue to one on `∐ X`.
For locally Noetherian `X i` this gives:

* `Chow.mem_ratEquiv_sigma_iff`: a `k`-cycle on `∐ X` is rationally equivalent to zero exactly
  when its restriction to every `X i` is;
* `Chow.ChowGroup.sigmaEquiv X k : CH_k(∐ X) ≃+ ∏ i, CH_k(X i)`, the Chow group of a coproduct is
  the product of the Chow groups of the summands, sending the class of a cycle to the classes of
  its restrictions (`Chow.ChowGroup.sigmaEquiv_cycleClass`).

Under either equivalence, pushforward along `Sigma.ι X i` inserts a cycle or Chow class in its
`i`-th coordinate (`Chow.cyclesSigmaEquiv_cyclesPushforward_sigmaι`,
`Chow.ChowGroup.sigmaEquiv_pushforward_sigmaι`).

The product is a genuine product, not a direct sum: for infinitely many summands a cycle on `∐ X`
can be nonzero on every one of them, as locally finite cycles need not have finite support. For a
finite index type it also identifies with the direct sum via `DirectSum.addEquivProd`.

## References

* [Stacks Project, Definition 42.19.1](https://stacks.math.columbia.edu/tag/02RW), where rational
  equivalence is defined through locally finite families of integral closed subschemes.
* W. Fulton, *Intersection Theory*, §1.3.
-/

public section

open AlgebraicGeometry Order CategoryTheory Limits Topology

universe u

namespace TauCeti.AlgebraicGeometry.Chow

variable {I : Type u} (X : I → Scheme.{u}) (k : ℤ)

section Cycles

/-- The restrictions of a `k`-cycle on `∐ X` to the summands, an additive map. The coprojections
are closed immersions, so they preserve the dimension of points. -/
private noncomputable def cyclesSigmaRestrict :
    cyclesOfDimension (∐ X) k →+ ((i : I) → cyclesOfDimension (X i) k) :=
  AddMonoidHom.mk'
    (fun α i ↦ ⟨Function.locallyFinsupp.comap (Sigma.ι X i) (Sigma.ι X i).continuous
        (Sigma.ι X i).isClosedEmbedding.injective (α : AlgebraicCycle (∐ X) ℤ), by
      rw [mem_cyclesOfDimension_iff, Function.locallyFinsupp.support_comap]
      intro y hy
      simpa only [mem_pointsOfDimension, Scheme.Hom.height_apply_eq_height] using
        mem_cyclesOfDimension_iff.mp α.property hy⟩)
    fun _ _ ↦ funext fun _ ↦ Subtype.ext (Function.locallyFinsupp.comap_add _ _ _ _ _)

private lemma cyclesSigmaRestrict_apply (α : cyclesOfDimension (∐ X) k) (i : I) (x : X i) :
    (cyclesSigmaRestrict X k α i : AlgebraicCycle (X i) ℤ) x =
      (α : AlgebraicCycle (∐ X) ℤ) (Sigma.ι X i x) :=
  Function.locallyFinsupp.comap_apply _ _ _ _ _

private lemma cyclesSigmaRestrict_injective : Function.Injective (cyclesSigmaRestrict X k) := by
  intro α β h
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
  obtain ⟨i, y, rfl⟩ := sigmaι_jointly_surjective X x
  rw [← cyclesSigmaRestrict_apply, ← cyclesSigmaRestrict_apply, h]

private lemma cyclesSigmaRestrict_surjective : Function.Surjective (cyclesSigmaRestrict X k) := by
  intro γ
  -- The sum of the pushforwards of the `γ i` along the coprojections, a locally finite sum since
  -- the summands form a locally finite family.
  have hc : LocallyFinite fun i ↦
      (cyclesPushforward (Sigma.ι X i) (γ i) : AlgebraicCycle (∐ X) ℤ).support :=
    (locallyFinite_range_sigmaι X).subset fun i ↦ by
      rw [coe_cyclesPushforward]
      exact AlgebraicCycle.support_map_subset_range _ _ _ _
  let α := Function.locallyFinsupp.locallyFiniteSum _ hc
  -- At a point of the summand `X i`, only the `i`-th pushforward contributes.
  have hα (i : I) (x : X i) : α (Sigma.ι X i x) = (γ i : AlgebraicCycle (X i) ℤ) x := by
    rw [Function.locallyFinsupp.locallyFiniteSum_apply,
      finsum_eq_single _ i fun j hj ↦ cyclesPushforward_apply_of_notMem_range _
        fun hx ↦ hj ((sigmaι_apply_mem_range_sigmaι_iff x).mp hx).symm]
    exact cyclesPushforward_apply _ x
  have hmem : α ∈ cyclesOfDimension (∐ X) k := by
    rw [mem_cyclesOfDimension_iff]
    intro x hx
    obtain ⟨i, y, rfl⟩ := sigmaι_jointly_surjective X x
    rw [Function.mem_support, hα] at hx
    simpa only [mem_pointsOfDimension, Scheme.Hom.height_apply_eq_height] using
      mem_cyclesOfDimension_iff.mp (γ i).property hx
  exact ⟨⟨α, hmem⟩, funext fun i ↦ Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦
    (cyclesSigmaRestrict_apply X k _ i x).trans (hα i x))⟩

/-- The `k`-cycles on a coproduct of schemes are the families of `k`-cycles on the summands: a
cycle on `∐ X` corresponds to its restrictions to the summands `X i`. -/
noncomputable def cyclesSigmaEquiv :
    cyclesOfDimension (∐ X) k ≃+ ((i : I) → cyclesOfDimension (X i) k) :=
  AddEquiv.ofBijective (cyclesSigmaRestrict X k)
    ⟨cyclesSigmaRestrict_injective X k, cyclesSigmaRestrict_surjective X k⟩

variable {X k}

/-- The restriction of a cycle on `∐ X` to `X i` has, at a point of `X i`, the coefficient of the
cycle at the image of the point. -/
@[simp]
lemma cyclesSigmaEquiv_apply (α : cyclesOfDimension (∐ X) k) (i : I) (x : X i) :
    (cyclesSigmaEquiv X k α i : AlgebraicCycle (X i) ℤ) x =
      (α : AlgebraicCycle (∐ X) ℤ) (Sigma.ι X i x) :=
  cyclesSigmaRestrict_apply X k α i x

/-- The cycle on `∐ X` with restrictions `γ` has, at the image of a point of `X i`, the
coefficient of `γ i` at that point. -/
@[simp]
lemma cyclesSigmaEquiv_symm_apply (γ : (i : I) → cyclesOfDimension (X i) k) (i : I) (x : X i) :
    ((cyclesSigmaEquiv X k).symm γ : AlgebraicCycle (∐ X) ℤ) (Sigma.ι X i x) =
      (γ i : AlgebraicCycle (X i) ℤ) x := by
  rw [← cyclesSigmaEquiv_apply, AddEquiv.apply_symm_apply]

/-- Under the coproduct equivalence for cycles, pushforward along a coprojection inserts a cycle
in the corresponding coordinate. -/
@[simp]
lemma cyclesSigmaEquiv_cyclesPushforward_sigmaι [DecidableEq I] (i : I)
    (α : cyclesOfDimension (X i) k) :
    cyclesSigmaEquiv X k (cyclesPushforward (Sigma.ι X i) α) = Pi.single i α := by
  funext j
  rcases eq_or_ne j i with rfl | h
  · rw [Pi.single_eq_same]
    exact Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ by
      rw [cyclesSigmaEquiv_apply, cyclesPushforward_apply])
  · rw [Pi.single_eq_of_ne h]
    exact Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ by
      rw [cyclesSigmaEquiv_apply]
      exact cyclesPushforward_apply_of_notMem_range α
        (fun hx ↦ h ((sigmaι_apply_mem_range_sigmaι_iff x).mp hx)))

end Cycles

section RatEquiv

namespace RatEquivFamily

variable {X k}

/-- The members of a family on `∐ X` lying in the summand `X i`, as a family on `X i`. -/
private noncomputable def restrictSigma (F : RatEquivFamily (∐ X) k) (i : I) :
    RatEquivFamily (X i) k where
  ι := {j : F.ι // Set.range (F.i j) ⊆ Set.range (Sigma.ι X i)}
  W j := F.W j.val
  i j := IsOpenImmersion.lift (Sigma.ι X i) (F.i j.val) j.property
  isClosedImmersion j := by
    have : IsClosedImmersion
        (IsOpenImmersion.lift (Sigma.ι X i) (F.i j.val) j.property ≫ Sigma.ι X i) := by
      rw [IsOpenImmersion.lift_fac]
      infer_instance
    exact .of_comp_isClosedImmersion _ (Sigma.ι X i)
  genericPoint_mem j := F.genericPoint_mem j.val
  r j := F.r j.val
  locallyFinite := by
    refine ((F.locallyFinite.comp_injective Subtype.val_injective).preimage_continuous
      (Sigma.ι X i).continuous).subset fun j ↦ ?_
    rintro _ ⟨w, rfl⟩
    exact ⟨w, by rw [← Scheme.Hom.comp_apply, IsOpenImmersion.lift_fac]⟩

private lemma sigmaι_apply_restrictSigma_i (F : RatEquivFamily (∐ X) k) (i : I)
    (j : (F.restrictSigma i).ι) (w : (F.restrictSigma i).W j) :
    Sigma.ι X i ((F.restrictSigma i).i j w) = F.i j.val w := by
  rw [← Scheme.Hom.comp_apply]
  exact congr($(IsOpenImmersion.lift_fac (Sigma.ι X i) (F.i j.val) j.property) w)

variable [∀ i, IsLocallyNoetherian (X i)]

private lemma component_restrictSigma_apply (F : RatEquivFamily (∐ X) k) (i : I)
    (j : (F.restrictSigma i).ι) (x : X i) :
    (F.restrictSigma i).component j x = F.component j.val (Sigma.ι X i x) := by
  by_cases hx : x ∈ Set.range ((F.restrictSigma i).i j)
  · obtain ⟨w, rfl⟩ := hx
    rw [(F.restrictSigma i).component_apply j w, sigmaι_apply_restrictSigma_i,
      F.component_apply j.val w]
    -- `F.restrictSigma i` keeps the subschemes and rational functions of `F`, by definition.
    rfl
  · rw [(F.restrictSigma i).component_apply_eq_zero_of_notMem_range j hx,
      F.component_apply_eq_zero_of_notMem_range j.val]
    rintro ⟨w, hw⟩
    exact hx ⟨w, (Sigma.ι X i).isOpenEmbedding.injective
      ((sigmaι_apply_restrictSigma_i F i j w).trans hw)⟩

/-- Restricting a family on `∐ X` to the summand `X i` restricts its cycle. -/
private lemma cycle_restrictSigma_apply (F : RatEquivFamily (∐ X) k) (i : I) (x : X i) :
    (F.restrictSigma i).cycle x = F.cycle (Sigma.ι X i x) := by
  -- Members of `F` lying in another summand vanish at the point `Sigma.ι X i x`.
  have hsupp : (Function.support fun j ↦ F.component j (Sigma.ι X i x)) ⊆
      Set.range (Subtype.val : (F.restrictSigma i).ι → F.ι) := by
    intro j hj
    obtain ⟨i', hi'⟩ := exists_range_subset_range_sigmaι X (F.i j)
    obtain rfl : i = i' := by
      by_contra hii'
      exact hj (F.component_apply_eq_zero_of_notMem_range j fun hx ↦
        hii' ((sigmaι_apply_mem_range_sigmaι_iff x).mp (hi' hx)))
    exact ⟨⟨j, hi'⟩, rfl⟩
  rw [cycle_apply, cycle_apply, ← Set.indicator_eq_self.mpr hsupp, ← finsum_mem_def,
    finsum_mem_range Subtype.val_injective]
  exact finsum_congr fun j ↦ component_restrictSigma_apply F i j x

omit [∀ i, IsLocallyNoetherian (X i)] in
/-- Families on the summands `X i`, glued to a family on `∐ X`. -/
private noncomputable def sigma (F : (i : I) → RatEquivFamily (X i) k) :
    RatEquivFamily (∐ X) k where
  ι := (i : I) × (F i).ι
  W p := (F p.fst).W p.snd
  i p := (F p.fst).i p.snd ≫ Sigma.ι X p.fst
  genericPoint_mem p := (F p.fst).genericPoint_mem p.snd
  r p := (F p.fst).r p.snd
  locallyFinite := by
    refine ((LocallyFinite.sigmaMk_image fun i ↦ (F i).locallyFinite).preimage_continuous
      (sigmaMk X).symm.continuous).subset ?_
    rintro ⟨i, j⟩ _ ⟨w, rfl⟩
    refine ⟨(F i).i j w, ⟨w, rfl⟩, ?_⟩
    apply (sigmaMk X).injective
    rw [Homeomorph.apply_symm_apply, sigmaMk_mk, Scheme.Hom.comp_apply]

/-- The cycle of the glued family has, at a point of `X i`, the coefficient of the cycle of `F i`.
-/
private lemma cycle_sigma_apply (F : (i : I) → RatEquivFamily (X i) k) (i : I) (x : X i) :
    (sigma F).cycle (Sigma.ι X i x) = (F i).cycle x := by
  -- Members glued from another summand vanish at the point `Sigma.ι X i x`.
  have hsupp : (Function.support fun p ↦ (sigma F).component p (Sigma.ι X i x)) ⊆
      Set.range (Sigma.mk i) := by
    rintro ⟨i', j⟩ hj
    obtain rfl : i = i' := by
      by_contra hii'
      refine hj ((sigma F).component_apply_eq_zero_of_notMem_range _ ?_)
      -- The `⟨i', j⟩`-th member is embedded through the summand `X i'`, by definition of `sigma`.
      exact fun ⟨w, hw⟩ ↦ hii' ((sigmaι_apply_mem_range_sigmaι_iff x).mp ⟨_, hw⟩)
    exact ⟨j, rfl⟩
  -- The members glued from `X i` are those of the pushforward of `F i` along the coprojection:
  -- both are `(F i).i j ≫ Sigma.ι X i` with the rational function `(F i).r j`, by definition.
  have hcomp (j : (F i).ι) :
      (sigma F).component ⟨i, j⟩ = ((F i).pushforward (Sigma.ι X i)).component j :=
    (component_def _ _).trans (component_def ((F i).pushforward (Sigma.ι X i)) j).symm
  rw [cycle_apply, ← Set.indicator_eq_self.mpr hsupp, ← finsum_mem_def]
  refine (finsum_mem_range (f := fun p : (sigma F).ι ↦ (sigma F).component p (Sigma.ι X i x))
    sigma_mk_injective).trans ?_
  refine (finsum_congr fun j ↦ congr($(hcomp j) (Sigma.ι X i x))).trans ?_
  refine (((F i).pushforward (Sigma.ι X i)).cycle_apply _).symm.trans ?_
  rw [cycle_pushforward, AlgebraicCycle.map_height_apply_of_isClosedImmersion]

end RatEquivFamily

variable {X k} [∀ i, IsLocallyNoetherian (X i)]

/-- A `k`-cycle on a coproduct of locally Noetherian schemes is rationally equivalent to zero
exactly when its restriction to every summand is. -/
theorem mem_ratEquiv_sigma_iff {α : cyclesOfDimension (∐ X) k} :
    α ∈ RatEquiv (∐ X) k ↔ ∀ i, cyclesSigmaEquiv X k α i ∈ RatEquiv (X i) k := by
  refine ⟨fun hα i ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨F, hF⟩ := mem_ratEquiv_iff.mp hα
    refine mem_ratEquiv_iff.mpr
      ⟨F.restrictSigma i, Function.locallyFinsuppWithin.ext fun x ↦ ?_⟩
    rw [RatEquivFamily.cycle_restrictSigma_apply, hF, cyclesSigmaEquiv_apply]
  · choose F hF using fun i ↦ mem_ratEquiv_iff.mp (h i)
    refine mem_ratEquiv_iff.mpr
      ⟨RatEquivFamily.sigma F, Function.locallyFinsuppWithin.ext fun x ↦ ?_⟩
    obtain ⟨i, y, rfl⟩ := sigmaι_jointly_surjective X x
    rw [RatEquivFamily.cycle_sigma_apply, hF, cyclesSigmaEquiv_apply]

namespace ChowGroup

variable (X k)

/-- The classes of the restrictions to the summands, defined on the Chow group of `∐ X`. -/
private noncomputable def sigmaHom : ChowGroup (∐ X) k →+ ((i : I) → ChowGroup (X i) k) :=
  lift (AddMonoidHom.pi fun i ↦ cycleClass.comp
      ((Pi.evalAddMonoidHom _ i).comp (cyclesSigmaEquiv X k).toAddMonoidHom))
    fun _ hα ↦ funext fun i ↦ cycleClass_eq_zero_iff.mpr (mem_ratEquiv_sigma_iff.mp hα i)

private lemma sigmaHom_cycleClass (α : cyclesOfDimension (∐ X) k) :
    sigmaHom X k (cycleClass α) = fun i ↦ cycleClass (cyclesSigmaEquiv X k α i) :=
  lift_cycleClass _ _ α

private lemma sigmaHom_bijective : Function.Bijective (sigmaHom X k) := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun a ha ↦ ?_, fun c ↦ ?_⟩
  · obtain ⟨α, rfl⟩ := cycleClass_surjective a
    rw [sigmaHom_cycleClass] at ha
    exact cycleClass_eq_zero_iff.mpr
      (mem_ratEquiv_sigma_iff.mpr fun i ↦ cycleClass_eq_zero_iff.mp (congr_fun ha i))
  · choose γ hγ using fun i ↦ cycleClass_surjective (c i)
    refine ⟨cycleClass ((cyclesSigmaEquiv X k).symm γ), ?_⟩
    rw [sigmaHom_cycleClass, AddEquiv.apply_symm_apply]
    exact funext hγ

/-- The Chow group of a coproduct of locally Noetherian schemes is the product of the Chow groups
of the summands: the class of a cycle goes to the classes of its restrictions to the summands. -/
noncomputable def sigmaEquiv : ChowGroup (∐ X) k ≃+ ((i : I) → ChowGroup (X i) k) :=
  AddEquiv.ofBijective (sigmaHom X k) (sigmaHom_bijective X k)

variable {X k}

/-- The identification of the Chow group of `∐ X` with the product sends the class of a cycle to
the classes of its restrictions to the summands. -/
@[simp]
lemma sigmaEquiv_cycleClass (α : cyclesOfDimension (∐ X) k) :
    sigmaEquiv X k (cycleClass α) = fun i ↦ cycleClass (cyclesSigmaEquiv X k α i) :=
  sigmaHom_cycleClass X k α

/-- The inverse identification sends a family of classes of cycles `γ i` on the summands to the
class of the cycle on `∐ X` with restrictions `γ`. -/
@[simp]
lemma sigmaEquiv_symm_cycleClass (γ : (i : I) → cyclesOfDimension (X i) k) :
    (sigmaEquiv X k).symm (fun i ↦ cycleClass (γ i)) =
      cycleClass ((cyclesSigmaEquiv X k).symm γ) := by
  rw [AddEquiv.symm_apply_eq, sigmaEquiv_cycleClass, AddEquiv.apply_symm_apply]

/-- Under the coproduct equivalence for Chow groups, pushforward along a coprojection inserts a
class in the corresponding coordinate. -/
@[simp]
lemma sigmaEquiv_pushforward_sigmaι [DecidableEq I] (i : I) (a : ChowGroup (X i) k) :
    sigmaEquiv X k (pushforward (Sigma.ι X i) a) = Pi.single i a := by
  obtain ⟨α, rfl⟩ := cycleClass_surjective a
  rw [pushforward_cycleClass, sigmaEquiv_cycleClass, cyclesSigmaEquiv_cyclesPushforward_sigmaι]
  exact (Pi.single_op (fun _ ↦ cycleClass) (fun _ ↦ map_zero _) i α).symm

end ChowGroup

end RatEquiv

end TauCeti.AlgebraicGeometry.Chow
