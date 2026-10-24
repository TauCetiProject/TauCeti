/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.EquationallyNoetherian
public import TauCeti.GroupTheory.GroupAlgGeom.Zariski
public import Mathlib.Topology.NoetherianSpace
import TauCeti.Topology.NoetherianSpace.Decomposition

/-!
# Noetherian Zariski topologies and irreducible components

Let `H` receive the coefficients `G` through `ι : G →* H`. Equational Noetherianity of `H` is the
descending chain condition on Zariski closed sets: `H` is equationally Noetherian exactly when the
Zariski topology on `H^X` is a Noetherian space for every finite type of variables `X`. Over an
equationally Noetherian group, every subset of `H^X` is in fact Zariski compact.

The closure of an irreducible set `Y` is the algebraic set `V_H(I_H(Y))`, without any domain
hypothesis on `H`, so every irreducible closed set is algebraic. Hence, over an equationally
Noetherian group, every closed set `Y ⊆ H^X` is an irredundant finite union `Y₁ ∪ ⋯ ∪ Yₘ` of
irreducible algebraic sets. The `Yᵢ` are the maximal irreducible subsets of `Y`, so the
decomposition is unique (`TauCeti.eq_setOf_maximal_isIrreducible_of_isAntichain`).

If the solution set of `S` is covered by those of systems `Tᵢ`, contained in it, the coordinate
group `G_{R(S)}` embeds in `∏ᵢ G_{R(Tᵢ)}` compatibly with the coefficients, because
`Rad_H(S) = ⋂ᵢ Rad_H(Tᵢ)`. Applied to the irreducible components, this embeds the coordinate group
of an algebraic set in the product of the coordinate groups of its components.

## Main definitions

* `TauCeti.GroupAlgGeom.CoordGroup.toPi`: the `G`-homomorphism `G_{R(S)} →* ∏ᵢ G_{R(Tᵢ)}`.

## Main results

* `TauCeti.GroupAlgGeom.isEquationallyNoetherian_iff_noetherianSpace`: `H` is equationally
  Noetherian if and only if the Zariski topology on `H^X` is Noetherian for every finite `X`.
* `TauCeti.GroupAlgGeom.closure_eq_V_I_of_isIrreducible`: the closure of an irreducible set is
  the algebraic set of its ideal.
* `TauCeti.GroupAlgGeom.IsEquationallyNoetherian.exists_irreducible_decomposition`: closed sets
  are irredundant finite unions of irreducible algebraic sets.
* `TauCeti.GroupAlgGeom.CoordGroup.toPi_injective`: the coordinate group embeds in the product of
  the coordinate groups of a covering family.
* `TauCeti.GroupAlgGeom.IsEquationallyNoetherian.exists_injective_coordGroup_toPi`: the coordinate
  group of an algebraic set embeds in the product of those of its irreducible components.

## References

* G. Baumslag, A. Myasnikov, V. Remeslennikov, *Algebraic geometry over groups I. Algebraic sets
  and ideal theory*, J. Algebra 219 (1999), §3.6, Proposition 10, Theorem D1, Corollaries 10–11
  and Proposition 12.
-/

public section

namespace TauCeti.GroupAlgGeom

open TopologicalSpace

variable {G H X : Type*} [Group G] [Group H] {ι : G →* H}

/-! ### Noetherianity of the Zariski topology -/

/-- Over an equationally Noetherian group, every set of points in finitely many variables is
compact in the Zariski topology. -/
theorem IsEquationallyNoetherian.isCompact (h : IsEquationallyNoetherian ι) [Finite X]
    (s : Set (X → H)) : @IsCompact (X → H) (zariskiTopology ι X) s := by
  let := zariskiTopology ι X
  refine isCompact_generateFrom (zariskiTopology_def ι X) fun P hP hsP ↦ ?_
  -- Each member of `P` is the complement of the solution set of some system; their union is the
  -- complement of the solutions of the union `T` of these systems.
  choose! S hS using fun U (hU : U ∈ P) ↦ hP hU
  let T : Set (GX G X) := ⋃ U ∈ P, S U
  obtain ⟨T₀, hT₀, hfin, hV⟩ := h.exists_finite T
  -- Each equation of the finite subsystem `T₀` comes from one member of `P`.
  have hU (w : T₀) : ∃ U ∈ P, w.1 ∈ S U := by simpa [T] using hT₀ w.2
  choose U hUP hwU using hU
  have : Finite T₀ := hfin
  refine ⟨Set.range U, Set.range_subset_iff.2 hUP, Set.finite_range U, fun v hv ↦ ?_⟩
  obtain ⟨W, hWP, hvW⟩ := hsP hv
  have hvT : v ∉ V ι T₀ := by
    rw [hV, mem_V]
    intro hvT
    rw [hS W hWP] at hvW
    exact hvW (mem_V.2 fun w hw ↦ hvT w (Set.mem_biUnion hWP hw))
  simp only [mem_V, not_forall] at hvT
  obtain ⟨w, hw, hvw⟩ := hvT
  refine Set.mem_sUnion.2 ⟨U ⟨w, hw⟩, Set.mem_range_self _, ?_⟩
  rw [hS _ (hUP _)]
  exact fun hv ↦ hvw (mem_V.1 hv w (hwU ⟨w, hw⟩))

/-- Over an equationally Noetherian group, the Zariski topology in finitely many variables is
Noetherian: closed sets satisfy the descending chain condition. -/
theorem IsEquationallyNoetherian.noetherianSpace (h : IsEquationallyNoetherian ι) [Finite X] :
    @NoetherianSpace (X → H) (zariskiTopology ι X) :=
  (@noetherianSpace_iff_isCompact _ (zariskiTopology ι X)).2 h.isCompact

/-- A group is equationally Noetherian if and only if its Zariski topology is Noetherian in every
finite type of variables. -/
theorem isEquationallyNoetherian_iff_noetherianSpace :
    IsEquationallyNoetherian ι ↔
      ∀ (X : Type*) [Finite X], @NoetherianSpace (X → H) (zariskiTopology ι X) := by
  refine ⟨fun h X _ ↦ h.noetherianSpace, fun h ↦ isEquationallyNoetherian_iff.2 fun X _ S ↦ ?_⟩
  let := zariskiTopology ι X
  have := h X
  -- The open complement of `V S` is compact and covered by the complements of the `V {s}`.
  obtain ⟨S₀, hS₀, hfin, hcover⟩ :=
    (NoetherianSpace.isCompact (V ι S)ᶜ).elim_finite_subcover_image
      (b := S) (c := fun s ↦ (V ι {s})ᶜ) (fun s _ ↦ (isClosed_V {s}).isOpen_compl)
      (fun v hv ↦ by
        simp only [Set.mem_compl_iff, mem_V, not_forall] at hv
        obtain ⟨s, hs, hvs⟩ := hv
        exact Set.mem_biUnion hs fun hv ↦ hvs (mem_V.1 hv s rfl))
  refine ⟨S₀, hS₀, hfin, (V_antitone ι hS₀).antisymm' fun v hv ↦ ?_⟩
  by_contra hvS
  obtain ⟨s, hs, hvs⟩ := Set.mem_iUnion₂.1 (hcover hvS)
  exact hvs (mem_V.2 fun t ht ↦ mem_V.1 hv t (Set.mem_singleton_iff.1 ht ▸ hs))

/-! ### Irreducible closed sets are algebraic -/

/-- The Zariski closure of an irreducible set is the algebraic set cut out by its ideal. No
domain hypothesis is needed. -/
theorem closure_eq_V_I_of_isIrreducible {Y : Set (X → H)}
    (hY : @IsIrreducible (X → H) (zariskiTopology ι X) Y) :
    @closure (X → H) (zariskiTopology ι X) Y = V ι (I ι Y) := by
  let := zariskiTopology ι X
  refine (closure_minimal (subset_V_I Y) (isClosed_V _)).antisymm fun v hv ↦ ?_
  let g : Set (Set (X → H)) := {U | ∃ S : Set (GX G X), U = (V ι S)ᶜ}
  have hopen {U : Set (X → H)} : @IsOpen _ (zariskiTopology ι X) U ↔ GenerateOpen g U := by
    rw [zariskiTopology_def]
    rfl
  -- Every open set missing `Y` misses `V (I Y)`; argue by induction on generated open sets,
  -- using irreducibility for intersections.
  have key (U : Set (X → H)) (hU : GenerateOpen g U) :
      Disjoint U Y → Disjoint U (V ι (I ι Y)) := by
    induction hU with
    | basic U hU =>
      obtain ⟨S, rfl⟩ := hU
      intro hUY
      have hYS : Y ⊆ V ι S := by simpa using hUY.subset_compl_left
      exact Set.disjoint_compl_left_iff_subset.2 (V_antitone ι (subset_I_iff.2 hYS))
    | univ => exact fun hUY ↦ absurd (Set.univ_disjoint.1 hUY) hY.nonempty.ne_empty
    | inter U₁ U₂ hU₁ hU₂ ih₁ ih₂ =>
      intro hUY
      by_cases h₁ : Disjoint U₁ Y
      · exact (ih₁ h₁).mono_left Set.inter_subset_left
      by_cases h₂ : Disjoint U₂ Y
      · exact (ih₂ h₂).mono_left Set.inter_subset_right
      rw [Set.not_disjoint_iff_nonempty_inter, Set.inter_comm] at h₁ h₂
      obtain ⟨w, hwY, hwU⟩ := hY.isPreirreducible U₁ U₂ (hopen.2 hU₁) (hopen.2 hU₂) h₁ h₂
      exact absurd hUY (Set.not_disjoint_iff.2 ⟨w, hwU, hwY⟩)
    | sUnion 𝒰 _ ih =>
      exact fun hUY ↦ Set.disjoint_sUnion_left.2 fun U hU ↦
        ih U hU (Set.disjoint_sUnion_left.1 hUY U hU)
  refine mem_closure_iff.2 fun U hU hvU ↦ Set.not_disjoint_iff_nonempty_inter.1 fun hUY ↦ ?_
  exact Set.disjoint_left.1 (key U (hopen.1 hU) hUY) hvU hv

/-- Every irreducible Zariski closed set is algebraic: it is cut out by its ideal. -/
theorem V_I_eq_of_isIrreducible_of_isClosed {Y : Set (X → H)}
    (hY : @IsIrreducible (X → H) (zariskiTopology ι X) Y)
    (hc : @IsClosed (X → H) (zariskiTopology ι X) Y) : V ι (I ι Y) = Y := by
  rw [← closure_eq_V_I_of_isIrreducible hY, @closure_eq_iff_isClosed _ (zariskiTopology ι X)]
  exact hc

/-! ### Irreducible components -/

/-- Over an equationally Noetherian group, every Zariski closed set in finitely many variables is
an irredundant finite union of irreducible algebraic sets. By
`TauCeti.eq_setOf_maximal_isIrreducible_of_isAntichain` these are the maximal irreducible subsets
of `Y`, so the decomposition is unique. -/
theorem IsEquationallyNoetherian.exists_irreducible_decomposition
    (h : IsEquationallyNoetherian ι) [Finite X] {Y : Set (X → H)}
    (hY : @IsClosed (X → H) (zariskiTopology ι X) Y) :
    ∃ 𝒴 : Set (Set (X → H)), 𝒴.Finite ∧
      (∀ Z ∈ 𝒴, @IsIrreducible (X → H) (zariskiTopology ι X) Z ∧ V ι (I ι Z) = Z) ∧
      IsAntichain (· ⊆ ·) 𝒴 ∧ Y = ⋃₀ 𝒴 := by
  let := zariskiTopology ι X
  have := h.noetherianSpace (X := X)
  obtain ⟨𝒴, hfin, hc, hi, hanti, rfl⟩ :=
    exists_finite_isAntichain_irreducible_of_noetherianSpace hY
  exact ⟨𝒴, hfin, fun Z hZ ↦ ⟨hi Z hZ, V_I_eq_of_isIrreducible_of_isClosed (hi Z hZ) (hc Z hZ)⟩,
    hanti, rfl⟩

/-! ### Coordinate groups of coverings -/

namespace CoordGroup

variable {κ : Type*}

variable (ι) in
/-- The canonical `G`-homomorphism `G_{R(S)} →* ∏ᵢ G_{R(Tᵢ)}` for systems `Tᵢ` whose solution
sets lie in that of `S`. -/
def toPi (S : Set (GX G X)) (T : κ → Set (GX G X)) (hT : ∀ i, V ι (T i) ⊆ V ι S) :
    GHom (coeff ι S) (MonoidHom.pi fun i ↦ coeff ι (T i)) where
  toMonoidHom := MonoidHom.pi fun i ↦
    QuotientGroup.map _ _ (.id _) (by simpa [Rad_def] using I_antitone ι (hT i))
  map_coeff' _ := by ext; simp

@[simp]
theorem toPi_mk (S : Set (GX G X)) (T : κ → Set (GX G X)) (hT : ∀ i, V ι (T i) ⊆ V ι S)
    (w : GX G X) (i : κ) :
    toPi ι S T hT (w : CoordGroup ι S) i = (w : CoordGroup ι (T i)) := by
  simp [toPi]

/-- If the solution set of `S` is covered by those of systems `Tᵢ` contained in it, then the
coordinate group of `S` embeds in the product of the coordinate groups of the `Tᵢ`. -/
theorem toPi_injective {S : Set (GX G X)} {T : κ → Set (GX G X)} (hT : ∀ i, V ι (T i) ⊆ V ι S)
    (hS : V ι S ⊆ ⋃ i, V ι (T i)) : Function.Injective (toPi ι S T hT) := by
  refine (injective_iff_map_eq_one _).2 fun q hq ↦ ?_
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
  have hw (i : κ) : w ∈ I ι (V ι (T i)) := by
    simpa [Rad_def] using congr_fun hq i
  rw [QuotientGroup.eq_one_iff, Rad_def]
  refine I_antitone ι hS ?_
  rw [I_iUnion]
  exact Subgroup.mem_iInf.2 hw

end CoordGroup

/-- Over an equationally Noetherian group, the solution set of a system `S` in finitely many
variables is an irredundant finite union of irreducible algebraic sets `V_H(T₁), …, V_H(Tₘ)`, and
the coordinate group `G_{R(S)}` embeds in `G_{R(T₁)} × ⋯ × G_{R(Tₘ)}` compatibly with the
coefficients. -/
theorem IsEquationallyNoetherian.exists_injective_coordGroup_toPi
    (h : IsEquationallyNoetherian ι) [Finite X] (S : Set (GX G X)) :
    ∃ (m : ℕ) (T : Fin m → Set (GX G X)) (hT : ∀ i, V ι (T i) ⊆ V ι S),
      (∀ i, @IsIrreducible (X → H) (zariskiTopology ι X) (V ι (T i))) ∧
      (∀ i j, V ι (T i) ⊆ V ι (T j) → i = j) ∧ V ι S = ⋃ i, V ι (T i) ∧
      Function.Injective (CoordGroup.toPi ι S T hT) := by
  obtain ⟨𝒴, hfin, hirr, hanti, hS⟩ := h.exists_irreducible_decomposition (isClosed_V S)
  -- Enumerate the components and take their ideals as defining systems.
  have := hfin.to_subtype
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin 𝒴
  let T : Fin m → Set (GX G X) := fun i ↦ I ι (e.symm i : Set (X → H))
  have hVT (i : Fin m) : V ι (T i) = e.symm i := (hirr _ (e.symm i).2).2
  have hU : V ι S = ⋃ i, V ι (T i) := by
    simp_rw [hVT, hS, Set.sUnion_eq_iUnion]
    exact (e.symm.surjective.iUnion_comp _).symm
  have hT (i : Fin m) : V ι (T i) ⊆ V ι S := hU ▸ Set.subset_iUnion (fun j ↦ V ι (T j)) i
  refine ⟨m, T, hT, fun i ↦ (hVT i).symm ▸ (hirr _ (e.symm i).2).1,
    fun i j hij ↦ e.symm.injective (Subtype.ext ?_), hU, CoordGroup.toPi_injective hT hU.le⟩
  rw [hVT, hVT] at hij
  exact hanti.eq (e.symm i).2 (e.symm j).2 hij

end TauCeti.GroupAlgGeom
