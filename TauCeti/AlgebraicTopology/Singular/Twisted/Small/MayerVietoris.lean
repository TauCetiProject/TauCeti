/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.Small.Chains
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The signed small-chain sequence with local coefficients

For subsets `U,V` of a space, twisted chains supported in `U ∩ V` map to the direct sum
of the chains supported in `U` and in `V` by `(i_U,-i_V)`. Addition maps this direct sum
onto the chains subordinate to the binary family `U,V`. These maps form a short exact
sequence of chain complexes, without any openness, freeness or finiteness hypothesis.

All coefficient fibres remain those of the given local system on the ambient space.
The support complexes here are the native `smallTwistedChainComplex` for singleton and
binary families. The target is the binary small-chain complex, not the chains supported
in the union: a simplex in the union need not lie in either member. This distinction is
essential when using the sequence to derive Mayer–Vietoris for an open cover.

The construction uses the coefficient characterization of `smallTwistedChains` and native
biproducts and short complexes. It does not choose a subdivision depth or a chain retraction.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2 (Mayer–Vietoris) and Section 3.H
  (local coefficients).
-/

public section

noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe u v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R] {X : TopCat.{v}}
  (L : LocalCoefficientSystem.{u, v, max v w} R X)

/-- Chains supported in the intersection are exactly the intersection of the two support
submodules. -/
lemma smallTwistedChains_inter (U V : Set X) (n : ℕ) :
    smallTwistedChains L (fun _ : Unit ↦ U ∩ V) n =
      smallTwistedChains L (fun _ : Unit ↦ U) n ⊓
        smallTwistedChains L (fun _ : Unit ↦ V) n := by
  ext c
  simp only [Submodule.mem_inf, mem_smallTwistedChains_iff,
    TopCat.mem_smallSingularSubcomplex_iff, Set.subset_inter_iff, exists_const]
  constructor
  · intro h
    exact ⟨fun σ hσ ↦ h σ (by tauto), fun σ hσ ↦ h σ (by tauto)⟩
  · rintro ⟨hU, hV⟩ σ hσ
    by_cases hu : Set.range (X.toSSetObjEquiv _ σ) ⊆ U
    · exact hV σ (by tauto)
    · exact hU σ hu

/-- Chains subordinate to a binary family are sums of chains supported in its members. -/
lemma smallTwistedChains_bool (U V : Set X) (n : ℕ) :
    smallTwistedChains L (Bool.rec U V) n =
      smallTwistedChains L (fun _ : Unit ↦ U) n ⊔
        smallTwistedChains L (fun _ : Unit ↦ V) n := by
  rw [smallTwistedChains_eq_iSup, iSup_bool_eq, sup_comm]

variable (U V : Set X)

private def interLeft : smallTwistedChainComplex L (fun _ : Unit ↦ U ∩ V) ⟶
    smallTwistedChainComplex L (fun _ : Unit ↦ U) :=
  smallTwistedChainComplexInclusion fun n ↦ by rw [smallTwistedChains_inter]; exact inf_le_left

private def interRight : smallTwistedChainComplex L (fun _ : Unit ↦ U ∩ V) ⟶
    smallTwistedChainComplex L (fun _ : Unit ↦ V) :=
  smallTwistedChainComplexInclusion fun n ↦ by rw [smallTwistedChains_inter]; exact inf_le_right

private def leftBool : smallTwistedChainComplex L (fun _ : Unit ↦ U) ⟶
    smallTwistedChainComplex L (Bool.rec U V) :=
  smallTwistedChainComplexInclusion fun n ↦ by rw [smallTwistedChains_bool]; exact le_sup_left

private def rightBool : smallTwistedChainComplex L (fun _ : Unit ↦ V) ⟶
    smallTwistedChainComplex L (Bool.rec U V) :=
  smallTwistedChainComplexInclusion fun n ↦ by rw [smallTwistedChains_bool]; exact le_sup_right

/-- The intersection map of the small twisted chain sequence, with sign `(i_U,-i_V)`. -/
def smallTwistedMayerVietorisToBiprod :
    smallTwistedChainComplex L (fun _ : Unit ↦ U ∩ V) ⟶
      smallTwistedChainComplex L (fun _ : Unit ↦ U) ⊞
        smallTwistedChainComplex L (fun _ : Unit ↦ V) :=
  biprod.lift (interLeft L U V) (-interRight L U V)

/-- The sum map from the two support complexes onto the binary small-chain complex. -/
def smallTwistedMayerVietorisFromBiprod :
    smallTwistedChainComplex L (fun _ : Unit ↦ U) ⊞
      smallTwistedChainComplex L (fun _ : Unit ↦ V) ⟶
        smallTwistedChainComplex L (Bool.rec U V) :=
  biprod.desc (leftBool L U V) (rightBool L U V)

/-- The first projection of the intersection map is the inclusion with positive sign. -/
@[reassoc (attr := simp)]
lemma smallTwistedMayerVietorisToBiprod_fst :
    smallTwistedMayerVietorisToBiprod L U V ≫ biprod.fst ≫
      smallTwistedChainComplexι L (fun _ : Unit ↦ U) =
        smallTwistedChainComplexι L (fun _ : Unit ↦ U ∩ V) := by
  simp [smallTwistedMayerVietorisToBiprod, interLeft]

/-- The second projection of the intersection map is minus the inclusion. -/
@[reassoc (attr := simp)]
lemma smallTwistedMayerVietorisToBiprod_snd :
    smallTwistedMayerVietorisToBiprod L U V ≫ biprod.snd ≫
      smallTwistedChainComplexι L (fun _ : Unit ↦ V) =
        -smallTwistedChainComplexι L (fun _ : Unit ↦ U ∩ V) := by
  simp [smallTwistedMayerVietorisToBiprod, interRight]

/-- The sum map followed by ambient inclusion adds the two ambient chains. -/
@[reassoc (attr := simp)]
lemma smallTwistedMayerVietorisFromBiprod_comp_ι :
    smallTwistedMayerVietorisFromBiprod L U V ≫ smallTwistedChainComplexι L (Bool.rec U V) =
      biprod.fst ≫ smallTwistedChainComplexι L (fun _ : Unit ↦ U) +
        biprod.snd ≫ smallTwistedChainComplexι L (fun _ : Unit ↦ V) := by
  apply biprod.hom_ext' <;> simp [smallTwistedMayerVietorisFromBiprod, leftBool, rightBool]

/-- In each degree, the first component of the signed map preserves the ambient chain. -/
lemma smallTwistedMayerVietorisToBiprod_fst_apply (n : ℕ)
    (c : (smallTwistedChainComplex L (fun _ : Unit ↦ U ∩ V)).X n) :
    (smallTwistedChainComplexι L (fun _ : Unit ↦ U)).f n
      ((biprod.fst : smallTwistedChainComplex L (fun _ : Unit ↦ U) ⊞
        smallTwistedChainComplex L (fun _ : Unit ↦ V) ⟶ _).f n
          ((smallTwistedMayerVietorisToBiprod L U V).f n c)) =
        (smallTwistedChainComplexι L (fun _ : Unit ↦ U ∩ V)).f n c := by
  simpa only [HomologicalComplex.comp_f, ModuleCat.comp_apply] using
    congrArg (fun k ↦ (k.f n).hom c) (smallTwistedMayerVietorisToBiprod_fst L U V)

/-- In each degree, the second component of the signed map negates the ambient chain. -/
lemma smallTwistedMayerVietorisToBiprod_snd_apply (n : ℕ)
    (c : (smallTwistedChainComplex L (fun _ : Unit ↦ U ∩ V)).X n) :
    (smallTwistedChainComplexι L (fun _ : Unit ↦ V)).f n
      ((biprod.snd : smallTwistedChainComplex L (fun _ : Unit ↦ U) ⊞
        smallTwistedChainComplex L (fun _ : Unit ↦ V) ⟶ _).f n
          ((smallTwistedMayerVietorisToBiprod L U V).f n c)) =
        -(smallTwistedChainComplexι L (fun _ : Unit ↦ U ∩ V)).f n c := by
  simpa only [HomologicalComplex.comp_f, ModuleCat.comp_apply,
    HomologicalComplex.neg_f_apply, ModuleCat.hom_neg, LinearMap.neg_apply] using
    congrArg (fun k ↦ (k.f n).hom c) (smallTwistedMayerVietorisToBiprod_snd L U V)

/-- In each degree, the sum map adds the ambient chains of the two projections. -/
lemma smallTwistedMayerVietorisFromBiprod_comp_ι_apply (n : ℕ)
    (c : (smallTwistedChainComplex L (fun _ : Unit ↦ U) ⊞
      smallTwistedChainComplex L (fun _ : Unit ↦ V)).X n) :
    (smallTwistedChainComplexι L (Bool.rec U V)).f n
      ((smallTwistedMayerVietorisFromBiprod L U V).f n c) =
        (smallTwistedChainComplexι L (fun _ : Unit ↦ U)).f n
          ((biprod.fst : smallTwistedChainComplex L (fun _ : Unit ↦ U) ⊞
            smallTwistedChainComplex L (fun _ : Unit ↦ V) ⟶ _).f n c) +
        (smallTwistedChainComplexι L (fun _ : Unit ↦ V)).f n
          ((biprod.snd : smallTwistedChainComplex L (fun _ : Unit ↦ U) ⊞
            smallTwistedChainComplex L (fun _ : Unit ↦ V) ⟶ _).f n c) := by
  simpa only [HomologicalComplex.comp_f, ModuleCat.comp_apply,
    HomologicalComplex.add_f_apply, ModuleCat.hom_add, LinearMap.add_apply] using
    congrArg (fun k ↦ (k.f n).hom c) (smallTwistedMayerVietorisFromBiprod_comp_ι L U V)

/-- The signed intersection map followed by addition is zero. -/
@[reassoc (attr := simp)]
lemma smallTwistedMayerVietorisToBiprod_fromBiprod :
    smallTwistedMayerVietorisToBiprod L U V ≫ smallTwistedMayerVietorisFromBiprod L U V = 0 := by
  apply (cancel_mono (smallTwistedChainComplexι L (Bool.rec U V))).1
  simp [smallTwistedMayerVietorisToBiprod, smallTwistedMayerVietorisFromBiprod,
    interLeft, interRight, leftBool, rightBool]

/-- The signed support sequence of small twisted singular chain complexes. -/
def smallTwistedMayerVietorisShortComplex :
    ShortComplex (ChainComplex (ModuleCat.{max v w} R) ℕ) :=
  ShortComplex.mk _ _ (smallTwistedMayerVietorisToBiprod_fromBiprod L U V)

/-- The support sequence has the signed intersection map and the sum map as its arrows. -/
lemma smallTwistedMayerVietorisShortComplex_def :
    smallTwistedMayerVietorisShortComplex L U V =
      ShortComplex.mk (smallTwistedMayerVietorisToBiprod L U V)
        (smallTwistedMayerVietorisFromBiprod L U V)
        (smallTwistedMayerVietorisToBiprod_fromBiprod L U V) := (rfl)

private lemma mono_smallTwistedMayerVietorisToBiprod (n : ℕ) :
    Mono ((smallTwistedMayerVietorisToBiprod L U V).f n) := by
  let A := smallTwistedChainComplex L (fun _ : Unit ↦ U)
  let B := smallTwistedChainComplex L (fun _ : Unit ↦ V)
  have h := congrArg (fun k ↦ k.f n) (smallTwistedMayerVietorisToBiprod_fst L U V)
  simp only [HomologicalComplex.comp_f] at h
  have : Mono ((smallTwistedMayerVietorisToBiprod L U V).f n ≫
      (biprod.fst : A ⊞ B ⟶ A).f n ≫
        (smallTwistedChainComplexι L (fun _ : Unit ↦ U)).f n) := by
    rw [h]
    infer_instance
  exact mono_of_mono _ ((biprod.fst : A ⊞ B ⟶ A).f n ≫
    (smallTwistedChainComplexι L (fun _ : Unit ↦ U)).f n)

private lemma epi_smallTwistedMayerVietorisFromBiprod (n : ℕ) :
    Epi ((smallTwistedMayerVietorisFromBiprod L U V).f n) := by
  apply (ModuleCat.epi_iff_surjective _).2
  intro c
  let iB := (smallTwistedChainComplexι L (Bool.rec U V)).f n
  have hc : iB.hom c ∈ smallTwistedChains L (Bool.rec U V) n := by
    rw [← range_smallTwistedChainComplexι_f]
    exact LinearMap.mem_range_self _ c
  rw [smallTwistedChains_bool, Submodule.mem_sup] at hc
  obtain ⟨a, ha, b, hb, hab⟩ := hc
  rw [← range_smallTwistedChainComplexι_f] at ha hb
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  let A := smallTwistedChainComplex L (fun _ : Unit ↦ U)
  let B := smallTwistedChainComplex L (fun _ : Unit ↦ V)
  refine ⟨((biprod.inl : A ⟶ A ⊞ B).f n).hom a' +
    ((biprod.inr : B ⟶ A ⊞ B).f n).hom b', ?_⟩
  apply (ModuleCat.mono_iff_injective
    ((smallTwistedChainComplexι L (Bool.rec U V)).f n)).1 inferInstance
  rw [smallTwistedMayerVietorisFromBiprod_comp_ι_apply]
  simpa only [map_add, ← ModuleCat.comp_apply,
    HomologicalComplex.biprod_inl_fst_f, HomologicalComplex.biprod_inl_snd_f,
    HomologicalComplex.biprod_inr_fst_f, HomologicalComplex.biprod_inr_snd_f,
    Category.id_comp, zero_comp, ModuleCat.hom_zero, LinearMap.zero_apply,
    add_zero, zero_add] using hab

private lemma exact_smallTwistedMayerVietoris (n : ℕ) :
    ((smallTwistedMayerVietorisShortComplex L U V).map
      (HomologicalComplex.eval _ _ n)).Exact := by
  apply (ShortComplex.moduleCat_exact_iff _).2
  intro c hc
  -- Fix the native biproduct degree carrier before evaluating sums of linear maps.
  dsimp only [smallTwistedMayerVietorisShortComplex, ShortComplex.map,
    HomologicalComplex.eval] at c hc ⊢
  let A := smallTwistedChainComplex L (fun _ : Unit ↦ U)
  let B := smallTwistedChainComplex L (fun _ : Unit ↦ V)
  let p := (biprod.fst : A ⊞ B ⟶ A).f n
  let q := (biprod.snd : A ⊞ B ⟶ B).f n
  let iU := (smallTwistedChainComplexι L (fun _ : Unit ↦ U)).f n
  let iV := (smallTwistedChainComplexι L (fun _ : Unit ↦ V)).f n
  -- Evaluation of the short complex is definitionally the degree component of the sum map.
  have hc' : (smallTwistedMayerVietorisFromBiprod L U V).f n c = 0 := hc
  have hsum : iU (p c) + iV (q c) = 0 := by
    rw [← smallTwistedMayerVietorisFromBiprod_comp_ι_apply, hc', map_zero]
  have ha : iU (p c) ∈ smallTwistedChains L (fun _ : Unit ↦ U ∩ V) n := by
    rw [smallTwistedChains_inter]
    constructor
    · rw [← range_smallTwistedChainComplexι_f]; exact LinearMap.mem_range_self _ _
    · rw [eq_neg_of_add_eq_zero_left hsum]
      apply Submodule.neg_mem
      rw [← range_smallTwistedChainComplexι_f]; exact LinearMap.mem_range_self _ _
  rw [← range_smallTwistedChainComplexι_f] at ha
  obtain ⟨z, hz⟩ := ha
  refine ⟨z, ?_⟩
  have hp : p ((smallTwistedMayerVietorisToBiprod L U V).f n z) = p c := by
    apply (ModuleCat.mono_iff_injective iU).1 inferInstance
    rw [smallTwistedMayerVietorisToBiprod_fst_apply]
    exact hz
  have hq : q ((smallTwistedMayerVietorisToBiprod L U V).f n z) = q c := by
    apply (ModuleCat.mono_iff_injective iV).1 inferInstance
    rw [smallTwistedMayerVietorisToBiprod_snd_apply, hz]
    exact neg_eq_of_add_eq_zero_right hsum
  -- The biproduct identity reconstructs the difference from its two zero projections.
  have h := congrArg (fun f ↦ f.hom
    ((smallTwistedMayerVietorisToBiprod L U V).f n z - c))
    (HomologicalComplex.biprod_total_f A B n)
  simp only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_comp,
    LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] at h
  rw [map_sub, hp, sub_self, map_zero, map_sub, hq, sub_self, map_zero, add_zero] at h
  exact sub_eq_zero.mp h.symm

/-- The signed small twisted chain sequence is short exact for every pair of subsets.
Its last term consists of simplices lying in either member, rather than arbitrary simplices
in their union. -/
theorem shortExact_smallTwistedMayerVietorisShortComplex :
    (smallTwistedMayerVietorisShortComplex L U V).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact { exact := exact_smallTwistedMayerVietoris L U V n
          mono_f := mono_smallTwistedMayerVietorisToBiprod L U V n
          epi_g := epi_smallTwistedMayerVietorisFromBiprod L U V n }

end TauCeti.LocalCoefficientSystem
