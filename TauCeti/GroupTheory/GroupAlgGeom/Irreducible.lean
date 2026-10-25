/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Zariski
public import TauCeti.GroupTheory.GroupAlgGeom.Discrimination
public import Mathlib.Topology.Irreducible

/-!
# Irreducible algebraic sets and discrimination

An irreducible algebraic set has a coordinate group discriminated by the target group:
finitely many nonidentity functions simultaneously remain nonidentity at some point.
Conversely, over a domain relative to the coefficients, discrimination of the coordinate
group implies irreducibility of the solution set. Neither finite generation of the variables
nor an equational Noetherian hypothesis is needed.

The coefficient homomorphism is arbitrary. Discrimination itself supplies a point, so the
equivalence also handles empty solution sets. If the coefficient image is trivial, the
domain hypothesis forces the target group to be trivial, and the nonempty solution set is
a singleton.

## References

* G. Baumslag, A. Myasnikov, V. Remeslennikov, *Algebraic geometry over groups I. Algebraic sets
  and ideal theory*, J. Algebra 219 (1999), §4, Lemma 15 and Theorem 5.
-/

public section

namespace TauCeti.GroupAlgGeom

variable {G H X : Type*} [Group G] [Group H] {ι : G →* H} {S : Set (GX G X)}

/-- Every irreducible solution set has a coordinate group discriminated by the target,
without any domain assumption. -/
theorem isDiscriminatedBy_coordGroup_of_isIrreducible
    (hS : @IsIrreducible (X → H) (zariskiTopology ι X) (V ι S)) :
    IsDiscriminatedBy (CoordGroup.coeff ι S) ι := by
  classical
  let := zariskiTopology ι X
  apply (isDiscriminatedBy_def _ _).mpr
  intro s hs
  choose w hw using (QuotientGroup.mk_surjective :
    Function.Surjective (fun w : GX G X => (w : CoordGroup ι S)))
  let U : CoordGroup ι S → Set (X → H) := fun q => (V ι {w q})ᶜ
  have hopen (q) : IsOpen (U q) := (isClosed_V {w q}).isOpen_compl
  have hne (q) (hq : q ∈ s) : (V ι S ∩ U q).Nonempty := by
    have hn : w q ∉ Rad ι S := fun h => hs q hq (hw q ▸
      (QuotientGroup.eq_one_iff (w q)).mpr h)
    obtain ⟨v, hv, he⟩ : ∃ v ∈ V ι S, eval ι v (w q) ≠ 1 := by
      simp only [mem_Rad] at hn
      push Not at hn
      exact hn
    exact ⟨v, hv, by simpa [U] using he⟩
  obtain ⟨v, hv, hvU⟩ := isIrreducible_iff_sInter.mp hS (s.image U)
    (by simpa only [Finset.forall_mem_image] using fun q _ => hopen q)
    (by simpa only [Finset.forall_mem_image] using hne)
  refine ⟨CoordGroup.evalGHom v hv, fun q hq => ?_⟩
  have he : eval ι v (w q) ≠ 1 := by
    simpa [U] using Set.mem_sInter.mp hvU _ (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
  rwa [← CoordGroup.evalGHom_mk hv (w q), hw q] at he

private theorem isPreirreducible_V_of_isDiscriminatedBy
    (hdom : IsGDomain ι) (hcoeff : ∃ g : G, ι g ≠ 1)
    (h : IsDiscriminatedBy (CoordGroup.coeff ι S) ι) :
    @IsPreirreducible (X → H) (zariskiTopology ι X) (V ι S) := by
  classical
  let := zariskiTopology ι X
  have hd := (isDiscriminatedBy_def _ _).mp h
  apply isPreirreducible_iff_isClosed_union_isClosed.mpr
  intro A B hA hB hcover
  obtain ⟨T, rfl⟩ := (isClosed_iff_V hdom hcoeff A).mp hA
  obtain ⟨U, rfl⟩ := (isClosed_iff_V hdom hcoeff B).mp hB
  by_contra hn
  obtain ⟨v, hv, hvT⟩ : ∃ v ∈ V ι S, v ∉ V ι T :=
    Set.not_subset.mp (not_or.mp hn).1
  obtain ⟨v', hv', hvU⟩ : ∃ v ∈ V ι S, v ∉ V ι U :=
    Set.not_subset.mp (not_or.mp hn).2
  obtain ⟨t, ht, hvt⟩ : ∃ t ∈ T, eval ι v t ≠ 1 := by
    simp only [mem_V] at hvT
    push Not at hvT
    exact hvT
  obtain ⟨u, hu, hvu⟩ : ∃ u ∈ U, eval ι v' u ≠ 1 := by
    simp only [mem_V] at hvU
    push Not at hvU
    exact hvU
  have ht1 : (t : CoordGroup ι S) ≠ 1 := fun e =>
    hvt (mem_Rad.mp ((QuotientGroup.eq_one_iff t).mp e) v hv)
  have hu1 : (u : CoordGroup ι S) ≠ 1 := fun e =>
    hvu (mem_Rad.mp ((QuotientGroup.eq_one_iff u).mp e) v' hv')
  obtain ⟨ψ, hψ⟩ := hd {(t : CoordGroup ι S), (u : CoordGroup ι S)}
    (by simpa using And.intro ht1 hu1)
  let p := CoordGroup.homEquiv ι S ψ
  have hψp : CoordGroup.evalGHom p.1 p.2 = ψ := by
    rw [← CoordGroup.homEquiv_symm_apply]
    exact (CoordGroup.homEquiv ι S).symm_apply_apply ψ
  have hpt : eval ι p.1 t ≠ 1 := by
    rw [← CoordGroup.evalGHom_mk p.2 t, hψp]
    exact hψ _ (by simp)
  have hpu : eval ι p.1 u ≠ 1 := by
    rw [← CoordGroup.evalGHom_mk p.2 u, hψp]
    exact hψ _ (by simp)
  rcases hcover p.2 with hp | hp
  · exact hpt (mem_V.mp hp t ht)
  · exact hpu (mem_V.mp hp u hu)

/-- Over a domain relative to arbitrary coefficients, a solution set is irreducible exactly
when its coordinate group is discriminated by the target. No nonemptiness hypothesis is
needed: discrimination, even on the empty finite family, supplies a point. -/
theorem isIrreducible_V_iff_isDiscriminatedBy (hdom : IsGDomain ι) :
    @IsIrreducible (X → H) (zariskiTopology ι X) (V ι S) ↔
      IsDiscriminatedBy (CoordGroup.coeff ι S) ι := by
  classical
  let := zariskiTopology ι X
  refine ⟨isDiscriminatedBy_coordGroup_of_isIrreducible, fun h => ?_⟩
  have hd := (isDiscriminatedBy_def _ _).mp h
  obtain ⟨φ, _⟩ := hd ∅ (by simp)
  have hne : (V ι S).Nonempty := ⟨(CoordGroup.homEquiv ι S φ).1,
    (CoordGroup.homEquiv ι S φ).2⟩
  refine ⟨hne, ?_⟩
  by_cases hcoeff : ∃ g : G, ι g ≠ 1
  · exact isPreirreducible_V_of_isDiscriminatedBy hdom hcoeff h
  · have hcoeff : ∀ g : G, ι g = 1 := by simpa using hcoeff
    have hall (x : H) : x = 1 := by
      by_contra hx
      apply (isGDomain_def ι).mp hdom x
      exact (isZeroDivisor_def ι x).mpr ⟨hx, x, hx, fun g => by simp [hcoeff]⟩
    have : Subsingleton H := ⟨fun x y => (hall x).trans (hall y).symm⟩
    exact Set.subsingleton_of_subsingleton.isPreirreducible

end TauCeti.GroupAlgGeom
