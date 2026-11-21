/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Chow.ClosedImmersion
public import TauCeti.AlgebraicGeometry.Scheme.Coproduct
import TauCeti.AlgebraicGeometry.Morphisms.ClosedImmersion.Basic
import TauCeti.Topology.LocallyFinite.Sigma
import TauCeti.Topology.LocallyFinsupp.Comap

/-!
# Chow groups of disjoint unions

For any small family of locally Noetherian schemes, restriction to the summands identifies
cycles, rational equivalence and Chow groups of the coproduct with their componentwise versions.
An integral closed subscheme lies in a single summand, and families of principal divisors on the
summands assemble to a locally finite family on the coproduct. This uses the locally finite
formulation of rational equivalence in Stacks Project, Remark 42.19.6.
For a finite index type the product of Chow groups is also a direct sum, via
`DirectSum.addEquivProd`.
-/

public section

open AlgebraicGeometry CategoryTheory Limits Order Set Topology TopologicalSpace

universe u

namespace TauCeti.AlgebraicGeometry.Chow

variable {ι : Type u} (X : ι → Scheme.{u}) (k : ℤ)

private theorem locallyFinite_support_cyclesPushforward (β : ∀ i, cyclesOfDimension (X i) k) :
    LocallyFinite fun i ↦
      (cyclesPushforward (Sigma.ι X i) (β i) : AlgebraicCycle (∐ X) ℤ).support := by
  intro z
  obtain ⟨⟨i, x⟩, rfl⟩ := (sigmaMk X).surjective z
  rw [sigmaMk_mk]
  refine ⟨range (Sigma.ι X i),
    (Sigma.ι X i).isOpenEmbedding.isOpen_range.mem_nhds (mem_range_self x),
    (finite_singleton i).subset ?_⟩
  rintro j ⟨_, hy, y, rfl⟩
  obtain ⟨w, hw⟩ := (mem_range_cyclesPushforward_iff (i := Sigma.ι X j)).mp ⟨β j, rfl⟩ hy
  exact congrArg Sigma.fst ((sigmaι_eq_iff X j i w y).1 hw)

private noncomputable def assembleCycles (β : ∀ i, cyclesOfDimension (X i) k) :
    cyclesOfDimension (∐ X) k :=
  ⟨Function.locallyFinsupp.locallyFiniteSum
    (fun i ↦ (cyclesPushforward (Sigma.ι X i) (β i) : AlgebraicCycle (∐ X) ℤ))
    (locallyFinite_support_cyclesPushforward X k β), mem_cyclesOfDimension_iff.mpr (by
    intro z hz
    rw [Function.mem_support, Function.locallyFinsupp.locallyFiniteSum_apply,
      ← finsum_mem_univ] at hz
    obtain ⟨i, _, hi⟩ := exists_ne_zero_of_finsum_mem_ne_zero hz
    exact mem_cyclesOfDimension_iff.mp (cyclesPushforward (Sigma.ι X i) (β i)).property hi)⟩

private theorem assembleCycles_apply (β : ∀ i, cyclesOfDimension (X i) k) (i : ι) (x : X i) :
    (assembleCycles X k β : AlgebraicCycle (∐ X) ℤ) (Sigma.ι X i x) =
      (β i : AlgebraicCycle (X i) ℤ) x := by
  simp only [assembleCycles, Function.locallyFinsupp.locallyFiniteSum_apply]
  refine (finsum_eq_single _ i fun j hj ↦ ?_).trans (cyclesPushforward_apply (β i) x)
  exact cyclesPushforward_apply_of_notMem_range _ fun ⟨y, hy⟩ ↦ hj <|
    congrArg Sigma.fst ((sigmaι_eq_iff X j i y x).1 hy)

/-- Restrict a cycle on a coproduct to its summands, preserving absolute dimension because the
inclusions are closed immersions. -/
noncomputable def cyclesCoproductEquiv : cyclesOfDimension (∐ X) k ≃+
    (∀ i, cyclesOfDimension (X i) k) := by
  let r (i : ι) (α : cyclesOfDimension (∐ X) k) : AlgebraicCycle (X i) ℤ :=
    Function.locallyFinsupp.comap (Sigma.ι X i) (Sigma.ι X i).continuous
      (Sigma.ι X i).isClosedEmbedding.injective (α : AlgebraicCycle (∐ X) ℤ)
  have hr (i : ι) (α : cyclesOfDimension (∐ X) k) (x : X i) :
      r i α x = (α : AlgebraicCycle (∐ X) ℤ) (Sigma.ι X i x) :=
    Function.locallyFinsupp.comap_apply _ _ _ (α : AlgebraicCycle (∐ X) ℤ) x
  refine
    { toFun := fun α i ↦ ⟨r i α, mem_cyclesOfDimension_iff.mpr fun x hx ↦ by
        rw [mem_pointsOfDimension, ← Scheme.Hom.height_apply_eq_height (Sigma.ι X i)]
        apply mem_pointsOfDimension.mp
        exact mem_cyclesOfDimension_iff.mp α.property
          (by simpa only [r, Function.locallyFinsupp.support_comap, mem_preimage] using hx)⟩
      invFun := assembleCycles X k
      left_inv := ?_
      right_inv := ?_
      map_add' := fun α β ↦ funext fun i ↦ Subtype.ext <|
        Function.locallyFinsupp.comap_add _ _ _ (α : AlgebraicCycle (∐ X) ℤ) β }
  · intro α
    apply Subtype.ext
    ext z
    obtain ⟨⟨i, x⟩, rfl⟩ := (sigmaMk X).surjective z
    rw [sigmaMk_mk, assembleCycles_apply, hr]
  · intro β
    funext i
    apply Subtype.ext
    ext x
    rw [hr, assembleCycles_apply]

/-- The coefficient of the restricted cycle at `x` is its coefficient at the image of `x`. -/
@[simp]
theorem cyclesCoproductEquiv_apply (α : cyclesOfDimension (∐ X) k) (i : ι) (x : X i) :
    (cyclesCoproductEquiv X k α i : AlgebraicCycle (X i) ℤ) x =
      (α : AlgebraicCycle (∐ X) ℤ) (Sigma.ι X i x) := by
  unfold cyclesCoproductEquiv
  exact Function.locallyFinsupp.comap_apply _ _ _ (α : AlgebraicCycle (∐ X) ℤ) x

/-- Assembling the summand cycles recovers each of their coefficients along its inclusion. -/
@[simp]
theorem cyclesCoproductEquiv_symm_apply (β : ∀ i, cyclesOfDimension (X i) k) (i : ι) (x : X i) :
    ((cyclesCoproductEquiv X k).symm β : AlgebraicCycle (∐ X) ℤ) (Sigma.ι X i x) =
      (β i : AlgebraicCycle (X i) ℤ) x := by
  rw [← cyclesCoproductEquiv_apply, AddEquiv.apply_symm_apply]

namespace RatEquivFamily

variable {X k}

/-- An integral support meets an open-and-closed summand exactly when its generic point lies
there; then the entire support lies in the summand. -/
private theorem range_subset_of_genericPoint_mem (F : RatEquivFamily (∐ X) k) (j : F.ι) (i : ι)
    (hj : F.i j (genericPoint (F.W j)) ∈ range (Sigma.ι X i)) :
    range (F.i j) ⊆ range (Sigma.ι X i) := by
  rintro _ ⟨x, rfl⟩
  exact ((genericPoint_specializes x).map (F.i j).continuous).mem_closed
    (Sigma.ι X i).isClosedEmbedding.isClosed_range hj

/-- Retain precisely the integral supports in summand `i`, leaving their rational functions
unchanged. -/
private noncomputable abbrev summand (F : RatEquivFamily (∐ X) k) (i : ι) :
    RatEquivFamily (X i) k where
  ι := {j : F.ι // F.i j (genericPoint (F.W j)) ∈ range (Sigma.ι X i)}
  W j := F.W j
  i j := IsOpenImmersion.lift (Sigma.ι X i) (F.i j)
    (F.range_subset_of_genericPoint_mem j i j.property)
  isClosedImmersion j := by
    have h := F.range_subset_of_genericPoint_mem j i j.property
    have : IsClosedImmersion (IsOpenImmersion.lift (Sigma.ι X i) (F.i j) h ≫ Sigma.ι X i) :=
      (IsOpenImmersion.lift_fac _ _ h).symm ▸ F.isClosedImmersion j
    exact IsClosedImmersion.of_comp_isClosedImmersion _ (Sigma.ι X i)
  isIntegral j := F.isIntegral j
  genericPoint_mem j := F.genericPoint_mem j
  r j := F.r j
  locallyFinite := by
    refine ((F.locallyFinite.comp_injective Subtype.coe_injective).preimage_continuous
      (Sigma.ι X i).continuous).subset fun j _ ⟨x, hx⟩ ↦ ?_
    refine ⟨x, ?_⟩
    rw [← hx, ← Scheme.Hom.comp_apply, IsOpenImmersion.lift_fac]

private theorem summand_comp (F : RatEquivFamily (∐ X) k) (i : ι) (j : (F.summand i).ι) :
    (F.summand i).i j ≫ Sigma.ι X i = F.i j.val :=
  IsOpenImmersion.lift_fac _ _ _

variable [∀ i, IsLocallyNoetherian (X i)]

private theorem cycle_summand_apply (F : RatEquivFamily (∐ X) k) (i : ι) (x : X i) :
    (F.summand i).cycle x = F.cycle (Sigma.ι X i x) := by
  have hcomp (j : (F.summand i).ι) :
      (F.summand i).component j x = F.component j.val (Sigma.ι X i x) := by
    by_cases hx : x ∈ range ((F.summand i).i j)
    · obtain ⟨w, rfl⟩ := hx
      rw [← Scheme.Hom.comp_apply, F.summand_comp, component_apply, component_apply]
    · rw [component_apply_eq_zero_of_notMem_range _ _ hx, eq_comm]
      apply component_apply_eq_zero_of_notMem_range
      rintro ⟨w, hw⟩
      apply hx
      refine ⟨w, (Sigma.ι X i).isClosedEmbedding.injective ?_⟩
      rwa [← Scheme.Hom.comp_apply, F.summand_comp]
  rw [cycle_apply, cycle_apply]
  refine (finsum_congr hcomp).trans ?_
  let s : Set F.ι := {j | F.i j (genericPoint (F.W j)) ∈ range (Sigma.ι X i)}
  refine (finsum_set_coe_eq_finsum_mem (f := fun j ↦ F.component j (Sigma.ι X i x)) s).trans ?_
  refine (finsum_mem_inter_support_eq' _ s univ fun j hj ↦ ⟨fun _ ↦ mem_univ _, fun _ ↦ ?_⟩).trans
    (finsum_mem_univ _)
  obtain ⟨w, hw⟩ := F.support_component_subset j hj
  exact ((genericPoint_specializes w).map (F.i j).continuous).mem_open
    (Sigma.ι X i).isOpenEmbedding.isOpen_range (hw ▸ mem_range_self x)

/-- Assemble the families on all summands without imposing a global finiteness condition. -/
private noncomputable abbrev assemble (F : ∀ i, RatEquivFamily (X i) k) :
    RatEquivFamily (∐ X) k where
  ι := Σ i, (F i).ι
  W j := (F j.1).W j.2
  i j := (F j.1).i j.2 ≫ Sigma.ι X j.1
  isIntegral j := (F j.1).isIntegral j.2
  genericPoint_mem j := (F j.1).genericPoint_mem j.2
  r j := (F j.1).r j.2
  locallyFinite := by
    have h := (LocallyFinite.sigmaMk_image (fun i ↦ (F i).locallyFinite)).preimage_continuous
      (sigmaMk X).symm.continuous
    refine h.subset fun j z ⟨w, hw⟩ ↦ ?_
    refine ⟨(F j.1).i j.2 w, mem_range_self _, (sigmaMk X).injective ?_⟩
    simpa only [sigmaMk_mk, Homeomorph.apply_symm_apply, ← Scheme.Hom.comp_apply] using hw

private theorem cycle_assemble_apply (F : ∀ i, RatEquivFamily (X i) k) (i : ι) (x : X i) :
    (assemble F).cycle (Sigma.ι X i x) = (F i).cycle x := by
  rw [cycle_apply, cycle_apply]
  refine (finsum_mem_univ _).symm.trans ((finsum_mem_inter_support_eq' _ univ
    (range (Sigma.mk i)) fun j hj ↦ ⟨fun _ ↦ ?_, fun _ ↦ mem_univ _⟩).trans ?_)
  · obtain ⟨w, hw⟩ := (assemble F).support_component_subset j hj
    rcases j with ⟨j, a⟩
    obtain rfl : j = i := congrArg Sigma.fst ((sigmaι_eq_iff X j i ((F j).i a w) x).mp
      (by simpa only [Scheme.Hom.comp_apply] using hw))
    exact mem_range_self a
  · rw [finsum_mem_range sigma_mk_injective]
    refine finsum_congr fun j ↦ ?_
    by_cases hx : x ∈ range ((F i).i j)
    · obtain ⟨w, rfl⟩ := hx
      exact ((assemble F).component_apply ⟨i, j⟩ w).trans ((F i).component_apply j w).symm
    · rw [(F i).component_apply_eq_zero_of_notMem_range _ hx]
      exact (assemble F).component_apply_eq_zero_of_notMem_range ⟨i, j⟩ fun ⟨w, hw⟩ ↦
        hx ⟨w, (Sigma.ι X i).isClosedEmbedding.injective hw⟩

end RatEquivFamily

variable [∀ i, IsLocallyNoetherian (X i)]

/-- A cycle on a coproduct is rationally equivalent to zero if and only if each restriction is. -/
theorem mem_ratEquiv_coproduct_iff (α : cyclesOfDimension (∐ X) k) :
    α ∈ RatEquiv (∐ X) k ↔ ∀ i, cyclesCoproductEquiv X k α i ∈ RatEquiv (X i) k := by
  simp only [mem_ratEquiv_iff]
  constructor
  · rintro ⟨F, hF⟩ i
    refine ⟨F.summand i, Function.locallyFinsuppWithin.ext fun x ↦ ?_⟩
    rw [F.cycle_summand_apply, hF, cyclesCoproductEquiv_apply]
  · intro h
    choose F hF using h
    refine ⟨RatEquivFamily.assemble F, Function.locallyFinsuppWithin.ext fun z ↦ ?_⟩
    obtain ⟨⟨i, x⟩, rfl⟩ := (sigmaMk X).surjective z
    rw [sigmaMk_mk, RatEquivFamily.cycle_assemble_apply, hF, cyclesCoproductEquiv_apply]

namespace ChowGroup

/-- Restriction gives an additive equivalence from the Chow group of a coproduct to the product
of the Chow groups of its summands. -/
noncomputable def coproductEquiv : ChowGroup (∐ X) k ≃+ (∀ i, ChowGroup (X i) k) := by
  let f := AddMonoidHom.pi fun i ↦ cycleClass.comp
    ((Pi.evalAddMonoidHom (fun i ↦ cyclesOfDimension (X i) k) i).comp
      (cyclesCoproductEquiv X k).toAddMonoidHom)
  let r := lift f fun α hα ↦ by
    rw [AddMonoidHom.mem_ker]
    funext i
    exact cycleClass_eq_zero_iff.mpr ((mem_ratEquiv_coproduct_iff X k α).mp hα i)
  have hr (α : cyclesOfDimension (∐ X) k) (i : ι) :
      r (cycleClass α) i = cycleClass (cyclesCoproductEquiv X k α i) :=
    congrFun (lift_cycleClass _ _ α) i
  refine AddEquiv.ofBijective r ⟨?_, ?_⟩
  · apply (injective_iff_map_eq_zero r).mpr
    intro a ha
    obtain ⟨α, rfl⟩ := cycleClass_surjective a
    apply cycleClass_eq_zero_iff.mpr ((mem_ratEquiv_coproduct_iff X k α).2 fun i ↦ ?_)
    exact cycleClass_eq_zero_iff.mp ((hr α i).symm.trans (congrFun ha i))
  · intro b
    choose β hβ using fun i ↦ cycleClass_surjective (b i)
    refine ⟨cycleClass ((cyclesCoproductEquiv X k).symm β), funext fun i ↦ ?_⟩
    rw [hr, AddEquiv.apply_symm_apply, hβ]

/-- Restriction on Chow groups sends a cycle class to the classes of the restricted cycles. -/
@[simp]
theorem coproductEquiv_cycleClass (α : cyclesOfDimension (∐ X) k) (i : ι) :
    coproductEquiv X k (cycleClass α) i = cycleClass (cyclesCoproductEquiv X k α i) :=
  congrFun (lift_cycleClass _ _ α) i

/-- Under the coproduct equivalence, pushforward from a summand is insertion in its coordinate. -/
@[simp]
theorem coproductEquiv_pushforward_sigmaι [DecidableEq ι] (i : ι) (a : ChowGroup (X i) k) :
    coproductEquiv X k (pushforward (Sigma.ι X i) a) = Pi.single i a := by
  obtain ⟨α, rfl⟩ := cycleClass_surjective a
  funext j
  rw [pushforward_cycleClass, coproductEquiv_cycleClass]
  by_cases h : i = j
  · subst j
    rw [Pi.single_eq_same]
    congr 1
    apply Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
    rw [cyclesCoproductEquiv_apply, cyclesPushforward_apply]
  · rw [Pi.single_eq_of_ne (Ne.symm h)]
    have hz : cyclesCoproductEquiv X k (cyclesPushforward (Sigma.ι X i) α) j = 0 := by
      apply Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
      rw [cyclesCoproductEquiv_apply]
      exact cyclesPushforward_apply_of_notMem_range α fun ⟨y, hy⟩ ↦
        h (congrArg Sigma.fst ((sigmaι_eq_iff X i j y x).mp hy))
    rw [hz, map_zero]

end ChowGroup
end TauCeti.AlgebraicGeometry.Chow
