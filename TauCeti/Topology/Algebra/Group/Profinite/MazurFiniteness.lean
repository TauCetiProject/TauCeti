/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.ProP.DualRank
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Topology.Algebra.IsUniformGroup.DiscreteSubgroup
import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicInt.Basic
import TauCeti.Topology.Algebra.Group.Quotient.Basic

/-!
# Mazur's finiteness condition

The condition `Φ_p` requires *every open subgroup* to have only finitely many continuous
characters into the discrete additive group of `𝔽_p`. For a profinite group this is equivalent
to topological finite generation of the maximal pro-`p` quotient of each open subgroup. In
particular, under `Φ_p` the maximal pro-`p` quotient of the open kernel of a residual
representation into a finite discrete group is topologically finitely generated. This is the
finiteness input for constructing Noetherian lifting rings.

## References

* Toby Gee, *Modularity lifting theorems*, §3.1.
* Mark Kisin, *Lectures on deformations of Galois representations*, Lecture 1, (1.2).
-/

public section

namespace TauCeti

variable {p : ℕ} {G : Type*} [Group G] [TopologicalSpace G]

/-- A group satisfies Mazur's condition at `p` if every open subgroup has finitely many
continuous additive `ZMod p`-valued characters. The condition for deformation theory is the
case of prime `p`. -/
def MazurFiniteness (p : ℕ) (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∀ U : OpenSubgroup G, Finite (continuousZModDual p U)

/-- The open-subgroup character criterion for Mazur's finiteness condition. -/
theorem mazurFiniteness_iff :
    MazurFiniteness p G ↔ ∀ U : OpenSubgroup G, Finite (continuousZModDual p U) :=
  Iff.rfl

/-- Mazur's condition passes to open subgroups. -/
theorem MazurFiniteness.openSubgroup (h : MazurFiniteness p G) (U : OpenSubgroup G) :
    MazurFiniteness p U := by
  apply mazurFiniteness_iff.mpr
  intro V
  have hW : IsOpen ((V.toSubgroup.map U.toSubgroup.subtype : Subgroup G) : Set G) := by
    rw [Subgroup.coe_map]
    exact U.isOpen.isOpenMap_subtypeVal _ V.isOpen
  let W : OpenSubgroup G := ⟨V.toSubgroup.map U.toSubgroup.subtype, hW⟩
  have hWU : W.toSubgroup ≤ U.toSubgroup := Subgroup.map_subtype_le V.toSubgroup
  have hV : W.toSubgroup.subgroupOf U.toSubgroup = V.toSubgroup :=
    Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _
  let e : V.toSubgroup ≃ₜ* W.toSubgroup :=
    hV ▸ Subgroup.subgroupOfContinuousMulEquivOfLe hWU
  have := mazurFiniteness_iff.mp h W
  exact Finite.of_surjective _ (e.continuousZModDualMap_bijective (n := p)).surjective

/-- For prime `p`, a compact topological group satisfies `Φ_p` exactly when each open subgroup
has topologically finitely generated maximal pro-`p` quotient. -/
theorem mazurFiniteness_iff_forall_isTopologicallyFinitelyGenerated_maximalProPQuotient
    [Fact p.Prime] [IsTopologicalGroup G] [CompactSpace G] :
    MazurFiniteness p G ↔
      ∀ U : OpenSubgroup G, IsTopologicallyFinitelyGenerated (maximalProPQuotient p U) := by
  rw [mazurFiniteness_iff]
  refine forall_congr' fun U ↦ ?_
  have : CompactSpace ↥U := isCompact_iff_compactSpace.mp U.isClosed.isCompact
  -- The discrete quotients defining the pro-`p` kernel separate points of the maximal quotient.
  have : TotallyDisconnectedSpace (maximalProPQuotient p U) := by
    refine totallyDisconnectedSpace_iff_connectedComponent_one.mpr
      (Set.Subset.antisymm ?_ (Set.singleton_subset_iff.mpr mem_connectedComponent))
    intro x hx
    obtain ⟨g, rfl⟩ := maximalProPQuotient.mk_surjective p U x
    refine Set.mem_singleton_iff.mpr ((QuotientGroup.eq_one_iff g).mpr ?_)
    refine mem_proPKernel_iff.mpr fun V hV ↦ ?_
    have := (TauCeti.QuotientGroup.continuous_mapOfLE (proPKernel_le hV)).mapsTo_connectedComponent
      1 hx
    simpa [QuotientGroup.eq_one_iff] using this
  have hP := isProP_maximalProPQuotient (p := p) (G := ↥U)
  rw [← hP.finite_continuousZModDual_iff, ← Module.finite_iff_finite (R := ZMod p)]
  exact (LinearMap.finite_iff_of_bijective _
    (maximalProPQuotient.continuousZModDualMap_bijective (p := p) (G := ↥U))).symm

/-- An open subgroup of a compact group satisfying `Φ_p` has topologically finitely generated
maximal pro-`p` quotient. -/
theorem MazurFiniteness.isTopologicallyFinitelyGenerated_maximalProPQuotient
    [Fact p.Prime] [IsTopologicalGroup G] [CompactSpace G] (h : MazurFiniteness p G)
    (U : OpenSubgroup G) : IsTopologicallyFinitelyGenerated (maximalProPQuotient p U) :=
  mazurFiniteness_iff_forall_isTopologicallyFinitelyGenerated_maximalProPQuotient.mp h U

/-- A topologically finitely generated compact topological group satisfies Mazur's condition:
its open subgroups are topologically finitely generated, and finitely many generators determine
any continuous character to a fixed finite discrete group. -/
theorem IsTopologicallyFinitelyGenerated.mazurFiniteness [IsTopologicalGroup G] [CompactSpace G]
    (h : IsTopologicallyFinitelyGenerated G) : MazurFiniteness p G := by
  apply mazurFiniteness_iff.mpr
  intro U
  by_cases hp : p = 0
  · subst p
    -- The discrete group `ZMod 0 = ℤ` has no nontrivial finite subgroup.
    have : CompactSpace ↥U := isCompact_iff_compactSpace.mp U.isClosed.isCompact
    have : Subsingleton (continuousZModDual 0 U) := ⟨fun χ ψ ↦ Additive.toMul.injective
      (χ.toMul.eq_one_of_isMulTorsionFree.trans ψ.toMul.eq_one_of_isMulTorsionFree.symm)⟩
    infer_instance
  · have : NeZero p := ⟨hp⟩
    have := (h.of_openSubgroup U).finite_monoidHom_isOpen_ker (Multiplicative (ZMod p))
    refine Finite.of_injective (fun χ : continuousZModDual p U ↦
      (⟨χ.toMul.toMonoidHom, χ.toMul.toMonoidHom.continuous_iff_isOpen_ker.mp χ.toMul.continuous⟩ :
        {f : U →* Multiplicative (ZMod p) // IsOpen (f.ker : Set U)})) fun _ _ hχψ ↦
      Additive.toMul.injective
        (ContinuousMonoidHom.toMonoidHom_injective (congrArg Subtype.val hχψ))

/-! ### Examples -/

-- The additive group of `p`-adic integers is topologically generated by `1`.
example (p : ℕ) [Fact p.Prime] : MazurFiniteness p (Multiplicative (PadicInt p)) :=
  (isTopologicallyFinitelyGenerated_multiplicative_padicInt p).mazurFiniteness

example : MazurFiniteness p (Multiplicative (ZMod 2)) :=
  isTopologicallyFinitelyGenerated_of_fg.mazurFiniteness

-- In contrast, the coordinate projections give infinitely many characters of a countable product.
example [Nontrivial (ZMod p)] : ¬ MazurFiniteness p (ℕ → Multiplicative (ZMod p)) := by
  classical
  intro h
  let U : OpenSubgroup (ℕ → Multiplicative (ZMod p)) := ⊤
  have := mazurFiniteness_iff.mp h U
  let χ (i : ℕ) : continuousZModDual p U := Additive.ofMul
    ⟨(Pi.evalMonoidHom _ i).comp U.toSubgroup.subtype,
      (continuous_apply i).comp continuous_subtypeVal⟩
  refine @not_finite ℕ _ (Finite.of_injective χ fun i j hij ↦ ?_)
  by_contra hne
  let x : U := ⟨Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod p)), by simp [U]⟩
  have hχ (k : ℕ) : (χ k).toMul x = (x : ℕ → Multiplicative (ZMod p)) k := (rfl)
  have he := congrArg (fun ψ : continuousZModDual p U ↦ ψ.toMul x) hij
  rw [hχ, hχ] at he
  have hji : j ≠ i := Ne.symm hne
  have he' : Multiplicative.ofAdd (1 : ZMod p) = 1 := by
    simpa only [x, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hji] using he
  exact (one_ne_zero : (1 : ZMod p) ≠ 0)
    (congrArg (fun y : Multiplicative (ZMod p) ↦ y.toAdd) he')

end TauCeti
