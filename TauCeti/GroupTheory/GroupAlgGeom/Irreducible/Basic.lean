/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Zariski
public import TauCeti.GroupTheory.GroupAlgGeom.Discrimination
public import Mathlib.Topology.Irreducible
import Mathlib.Topology.Bases

/-!
# Irreducible algebraic sets and discrimination

An irreducible algebraic set has a coordinate group discriminated by the target group:
finitely many nonidentity functions simultaneously remain nonidentity at some point.
Conversely, discrimination of the coordinate group implies irreducibility of the solution
set. Neither a domain assumption, finite generation of the variables, nor an equational
Noetherian hypothesis is needed.

The coefficient homomorphism is arbitrary. Discrimination itself supplies a point, so the
equivalence also handles empty solution sets, trivial coefficient images, and arbitrary
target groups.

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
    (h : IsDiscriminatedBy (CoordGroup.coeff ι S) ι) :
    @IsPreirreducible (X → H) (zariskiTopology ι X) (V ι S) := by
  classical
  let := zariskiTopology ι X
  let B : Set (Set (X → H)) := {U | ∃ T : Set (GX G X), U = (V ι T)ᶜ}
  -- Discrimination makes finite families of generating opens meet simultaneously.
  have hfinite (F : Set (Set (X → H))) (hF : F.Finite) (hFB : F ⊆ B)
      (hne : ∀ U ∈ F, (V ι S ∩ U).Nonempty) : (V ι S ∩ ⋂₀ F).Nonempty := by
    let := hF.fintype
    have hw (U : F) : ∃ w : GX G X, (w : CoordGroup ι S) ≠ 1 ∧
        ∀ v : X → H, eval ι v w ≠ 1 → v ∈ U.1 := by
      obtain ⟨T, hT⟩ := hFB U.2
      obtain ⟨v, hv, hvU⟩ := hne U.1 U.2
      have hvT : v ∉ V ι T := by simpa only [hT, Set.mem_compl_iff] using hvU
      obtain ⟨w, hwT, hvw⟩ : ∃ w ∈ T, eval ι v w ≠ 1 := by
        simp only [mem_V] at hvT
        push Not at hvT
        exact hvT
      refine ⟨w, fun e => hvw (mem_Rad.mp ((QuotientGroup.eq_one_iff w).mp e) v hv), ?_⟩
      intro v he
      rw [hT]
      exact fun hv => he (mem_V.mp hv w hwT)
    choose w hw1 hwU using hw
    obtain ⟨ψ, hψ⟩ := (isDiscriminatedBy_def _ _).mp h
      (Finset.univ.image fun U : F => (w U : CoordGroup ι S))
      (by simpa only [Finset.forall_mem_image, Finset.mem_univ, forall_const] using hw1)
    let p := CoordGroup.homEquiv ι S ψ
    have hψp : CoordGroup.evalGHom p.1 p.2 = ψ := by
      rw [← CoordGroup.homEquiv_symm_apply]
      exact (CoordGroup.homEquiv ι S).symm_apply_apply ψ
    refine ⟨p.1, p.2, Set.mem_sInter.mpr fun U hUF => ?_⟩
    apply hwU ⟨U, hUF⟩ p.1
    rw [← CoordGroup.evalGHom_mk p.2, hψp]
    exact hψ _ (Finset.mem_image.mpr ⟨⟨U, hUF⟩, Finset.mem_univ _, rfl⟩)
  -- Refine arbitrary open neighborhoods to finite intersections of generating opens.
  have hb := TopologicalSpace.isTopologicalBasis_of_subbasis
    (zariskiTopology_eq_generateFrom ι X)
  intro U W hU hW ⟨u, hu, huU⟩ ⟨v, hv, hvW⟩
  obtain ⟨_, ⟨F, ⟨hF, hFB⟩, rfl⟩, huF, hFU⟩ :=
    hb.exists_subset_of_mem_open huU hU
  obtain ⟨_, ⟨K, ⟨hK, hKB⟩, rfl⟩, hvK, hKW⟩ :=
    hb.exists_subset_of_mem_open hvW hW
  obtain ⟨p, hp, hpFK⟩ := hfinite (F ∪ K) (hF.union hK) (Set.union_subset hFB hKB)
    (fun A hA => hA.elim
      (fun hAF => ⟨u, hu, Set.mem_sInter.mp huF A hAF⟩)
      (fun hAK => ⟨v, hv, Set.mem_sInter.mp hvK A hAK⟩))
  rw [Set.sInter_union] at hpFK
  exact ⟨p, hp, hFU hpFK.1, hKW hpFK.2⟩

/-- A solution set over arbitrary coefficients is irreducible exactly when its coordinate
group is discriminated by the target. No domain or nonemptiness hypothesis is needed:
discrimination, even on the empty finite family, supplies a point. -/
theorem isIrreducible_V_iff_isDiscriminatedBy :
    @IsIrreducible (X → H) (zariskiTopology ι X) (V ι S) ↔
      IsDiscriminatedBy (CoordGroup.coeff ι S) ι := by
  classical
  let := zariskiTopology ι X
  refine ⟨isDiscriminatedBy_coordGroup_of_isIrreducible, fun h => ?_⟩
  have hd := (isDiscriminatedBy_def _ _).mp h
  obtain ⟨φ, _⟩ := hd ∅ (by simp)
  have hne : (V ι S).Nonempty := ⟨(CoordGroup.homEquiv ι S φ).1,
    (CoordGroup.homEquiv ι S φ).2⟩
  exact ⟨hne, isPreirreducible_V_of_isDiscriminatedBy h⟩

end TauCeti.GroupAlgGeom
