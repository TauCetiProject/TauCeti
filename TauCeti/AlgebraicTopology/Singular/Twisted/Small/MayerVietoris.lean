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
  apply le_antisymm
  · simpa only [Submodule.comap_id] using
      (smallTwistedChains_le_comap L (Bool.rec U V) (LinearMap.id)
        (smallTwistedChains L (fun _ : Unit ↦ U) n ⊔
          smallTwistedChains L (fun _ : Unit ↦ V) n) (by
        intro σ hσ x
        obtain ⟨i, hi⟩ := (TopCat.mem_smallSingularSubcomplex_iff X _ σ).1 hσ
        cases i with
        | false =>
          exact Submodule.mem_sup_left (ιTwistedChainComplex_mem_smallTwistedChains L _
            ((TopCat.mem_smallSingularSubcomplex_iff X _ σ).2 ⟨(), hi⟩) x)
        | true =>
          exact Submodule.mem_sup_right (ιTwistedChainComplex_mem_smallTwistedChains L _
            ((TopCat.mem_smallSingularSubcomplex_iff X _ σ).2 ⟨(), hi⟩) x)))
  · exact sup_le
      (smallTwistedChains_mono L (fun _ : Unit ↦ U) (Bool.rec U V)
        (fun _ ↦ false) (fun _ ↦ Set.Subset.rfl) n)
      (smallTwistedChains_mono L (fun _ : Unit ↦ V) (Bool.rec U V)
        (fun _ ↦ true) (fun _ ↦ Set.Subset.rfl) n)

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
def smallTwistedMayerVietorisF :
    smallTwistedChainComplex L (fun _ : Unit ↦ U ∩ V) ⟶
      smallTwistedChainComplex L (fun _ : Unit ↦ U) ⊞
        smallTwistedChainComplex L (fun _ : Unit ↦ V) :=
  biprod.lift (interLeft L U V) (-interRight L U V)

/-- The sum map from the two support complexes onto the binary small-chain complex. -/
def smallTwistedMayerVietorisG :
    smallTwistedChainComplex L (fun _ : Unit ↦ U) ⊞
      smallTwistedChainComplex L (fun _ : Unit ↦ V) ⟶
        smallTwistedChainComplex L (Bool.rec U V) :=
  biprod.desc (leftBool L U V) (rightBool L U V)

/-- The first projection of the intersection map is the inclusion with positive sign. -/
@[reassoc (attr := simp)]
lemma smallTwistedMayerVietorisF_fst :
    smallTwistedMayerVietorisF L U V ≫ biprod.fst ≫
      smallTwistedChainComplexι L (fun _ : Unit ↦ U) =
        smallTwistedChainComplexι L (fun _ : Unit ↦ U ∩ V) := by
  simp [smallTwistedMayerVietorisF, interLeft]

/-- The second projection of the intersection map is minus the inclusion. -/
@[reassoc (attr := simp)]
lemma smallTwistedMayerVietorisF_snd :
    smallTwistedMayerVietorisF L U V ≫ biprod.snd ≫
      smallTwistedChainComplexι L (fun _ : Unit ↦ V) =
        -smallTwistedChainComplexι L (fun _ : Unit ↦ U ∩ V) := by
  simp [smallTwistedMayerVietorisF, interRight]

/-- The sum map followed by ambient inclusion adds the two ambient chains. -/
@[reassoc (attr := simp)]
lemma smallTwistedMayerVietorisG_comp_ι :
    smallTwistedMayerVietorisG L U V ≫ smallTwistedChainComplexι L (Bool.rec U V) =
      biprod.fst ≫ smallTwistedChainComplexι L (fun _ : Unit ↦ U) +
        biprod.snd ≫ smallTwistedChainComplexι L (fun _ : Unit ↦ V) := by
  apply biprod.hom_ext' <;> simp [smallTwistedMayerVietorisG, leftBool, rightBool]

/-- The signed intersection map followed by addition is zero. -/
@[reassoc (attr := simp)]
lemma smallTwistedMayerVietorisF_comp_G :
    smallTwistedMayerVietorisF L U V ≫ smallTwistedMayerVietorisG L U V = 0 := by
  apply (cancel_mono (smallTwistedChainComplexι L (Bool.rec U V))).1
  simp [smallTwistedMayerVietorisF, smallTwistedMayerVietorisG, interLeft, interRight,
    leftBool, rightBool]

/-- The signed support sequence of small twisted singular chain complexes. -/
def smallTwistedMayerVietorisShortComplex :
    ShortComplex (ChainComplex (ModuleCat.{max v w} R) ℕ) :=
  ShortComplex.mk _ _ (smallTwistedMayerVietorisF_comp_G L U V)

/-- The support sequence has the signed intersection map and the sum map as its arrows. -/
lemma smallTwistedMayerVietorisShortComplex_def :
    smallTwistedMayerVietorisShortComplex L U V =
      ShortComplex.mk (smallTwistedMayerVietorisF L U V)
        (smallTwistedMayerVietorisG L U V) (smallTwistedMayerVietorisF_comp_G L U V) := (rfl)

private lemma mono_f_smallTwistedMayerVietoris (n : ℕ) :
    Mono ((smallTwistedMayerVietorisF L U V).f n) := by
  apply (ModuleCat.mono_iff_injective _).2
  intro a b hab
  apply (ModuleCat.mono_iff_injective
    ((smallTwistedChainComplexι L (fun _ : Unit ↦ U ∩ V)).f n)).1 inferInstance
  have h := congrArg (fun k ↦ (k.f n).hom a) (smallTwistedMayerVietorisF_fst L U V)
  have h' := congrArg (fun k ↦ (k.f n).hom b) (smallTwistedMayerVietorisF_fst L U V)
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply] at h h'
  rw [hab] at h
  exact h.symm.trans h'

private lemma epi_g_smallTwistedMayerVietoris (n : ℕ) :
    Epi ((smallTwistedMayerVietorisG L U V).f n) := by
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
  rw [map_add, map_add]
  have hU : (biprod.inl : A ⟶ A ⊞ B) ≫ smallTwistedMayerVietorisG L U V ≫
      smallTwistedChainComplexι L (Bool.rec U V) =
        smallTwistedChainComplexι L (fun _ : Unit ↦ U) := by simp [A, B]
  have hV : (biprod.inr : B ⟶ A ⊞ B) ≫ smallTwistedMayerVietorisG L U V ≫
      smallTwistedChainComplexι L (Bool.rec U V) =
        smallTwistedChainComplexι L (fun _ : Unit ↦ V) := by simp [A, B]
  simpa only [HomologicalComplex.comp_f, ModuleCat.comp_apply] using
    (congrArg₂ (· + ·) (congrArg (fun k ↦ (k.f n).hom a') hU)
      (congrArg (fun k ↦ (k.f n).hom b') hV)).trans hab

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
  have hsum : iU (p c) + iV (q c) = 0 := by
    have h := congrArg (fun k ↦ (k.f n).hom c) (smallTwistedMayerVietorisG_comp_ι L U V)
    have hc' : (smallTwistedMayerVietorisG L U V).f n c = 0 := hc
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.add_f_apply,
      ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
      hc', map_zero] using h.symm
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
  have hp : p ((smallTwistedMayerVietorisF L U V).f n z) = p c := by
    apply (ModuleCat.mono_iff_injective iU).1 inferInstance
    have h := congrArg (fun k ↦ (k.f n).hom z) (smallTwistedMayerVietorisF_fst L U V)
    exact h.trans hz
  have hq : q ((smallTwistedMayerVietorisF L U V).f n z) = q c := by
    apply (ModuleCat.mono_iff_injective iV).1 inferInstance
    have h := congrArg (fun k ↦ (k.f n).hom z) (smallTwistedMayerVietorisF_snd L U V)
    exact h.trans ((congrArg Neg.neg hz).trans (neg_eq_of_add_eq_zero_right hsum))
  have h := congrArg (fun f ↦ f.hom ((smallTwistedMayerVietorisF L U V).f n z))
    (HomologicalComplex.biprod_total_f A B n)
  have h' := congrArg (fun f ↦ f.hom c) (HomologicalComplex.biprod_total_f A B n)
  simp only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_comp,
    LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] at h h'
  rw [hp, hq] at h
  exact h.symm.trans h'

/-- The signed small twisted chain sequence is short exact for every pair of subsets.
Its last term consists of simplices lying in either member, rather than arbitrary simplices
in their union. -/
theorem shortExact_smallTwistedMayerVietorisShortComplex :
    (smallTwistedMayerVietorisShortComplex L U V).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact { exact := exact_smallTwistedMayerVietoris L U V n
          mono_f := mono_f_smallTwistedMayerVietoris L U V n
          epi_g := epi_g_smallTwistedMayerVietoris L U V n }

end TauCeti.LocalCoefficientSystem
