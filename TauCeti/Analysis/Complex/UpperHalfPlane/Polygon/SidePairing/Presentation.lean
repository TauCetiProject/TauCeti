/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.Relations
public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.Tessellation
public import Mathlib.GroupTheory.PresentedGroup
import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.Macbeath
import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.Neighbours

/-!
# The relator quotient of a side-paired polygon

The side-identification words and finite-vertex cycle words of a side-paired hyperbolic polygon
give a group presented by generators indexed by sides. Evaluating the generators in a group
containing the side-pairing transformations factors through this presented group. For a locally
finite fundamental polygon, this map is an isomorphism onto the group: this is the presentation
part of Poincaré's polygon theorem.

An ideal vertex contributes no finite-order relation. At a finite vertex the cycle word is
raised to the order of its cycle transformation, so its image is the identity.

Injectivity is deduced from Macbeath's presentation of the group by the translates meeting the
polygon, `ConvexPolygon.SidePairing.macbeathHom_bijective`. Each such translate is the identity,
a side neighbour, or an inverse partial cycle tile at a finite vertex, and so has a word in the
side generators. Distinct descriptions of one translate give the same element of the relator
quotient: two vertices of one translate are the endpoints of a common side, by convexity. Three
distinct tiles meet only at a finite vertex, where the Macbeath relation follows from the cycle
relation. This gives an inverse of the evaluation map.

## Main results

* `ConvexPolygon.SidePairing.relatorQuotientTo_surjective`: the side-pairing maps generate the
  group of a locally finite fundamental polygon.
* `ConvexPolygon.SidePairing.relatorQuotientTo_injective`: the side and finite-vertex cycle
  relations imply every relation among the side-pairing maps.
* `ConvexPolygon.SidePairing.ker_lift_generatorsIn_eq_normalClosure_relators`: the same statement
  as an equality of subgroups of the free group on the sides.

## References

* A. M. Macbeath, *Groups of homeomorphisms of a simply connected space*, Ann. of Math. (2) 79
  (1964), 473–488.
* Alan Beardon, *The Geometry of Discrete Groups*, Chapter 9.
* Svetlana Katok, *Fuchsian Groups*, Chapter 3.
-/

public section

noncomputable section

open Set UpperHalfPlane
open scoped MatrixGroups Pointwise

namespace TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing

variable {n : ℕ} [NeZero n] {P : ConvexPolygon n} (σ : P.SidePairing)

/-- The side-identification and finite-vertex cycle relators of a side pairing. -/
def relators : Set (FreeGroup (Fin n)) :=
  range σ.sideRelator ∪
    {w | ∃ (j : Fin n) (z : ℍ), P.vertex j = .inl z ∧
      w = σ.cycleWord j ^ orderOf (σ.cycleMap j)}

/-- A word is a relator exactly when it is a side-identification word or a finite-vertex cycle
power. -/
@[simp]
theorem mem_relators_iff {w : FreeGroup (Fin n)} :
    w ∈ σ.relators ↔
      (∃ i, σ.sideRelator i = w) ∨
        (∃ (j : Fin n) (z : ℍ), P.vertex j = .inl z ∧
          w = σ.cycleWord j ^ orderOf (σ.cycleMap j)) := by
  simp [relators]

/-- A side-identification word belongs to the relator set. -/
theorem sideRelator_mem_relators (i : Fin n) : σ.sideRelator i ∈ σ.relators :=
  Or.inl ⟨i, rfl⟩

/-- The order relation of a finite vertex belongs to the relator set. -/
theorem cycleWord_pow_mem_relators {j : Fin n} {z : ℍ} (hj : P.vertex j = .inl z) :
    σ.cycleWord j ^ orderOf (σ.cycleMap j) ∈ σ.relators :=
  Or.inr ⟨j, z, hj, rfl⟩

/-- Every displayed relator evaluates to the identity in the projective group. -/
theorem pairingHom_eq_one_of_mem_relators {w : FreeGroup (Fin n)} (hw : w ∈ σ.relators) :
    σ.pairingHom w = 1 := by
  rcases hw with ⟨i, rfl⟩ | ⟨j, z, _, rfl⟩
  · simp
  · simp

/-- The quotient of the free side group by the side and finite-vertex cycle relations. -/
abbrev RelatorQuotient := PresentedGroup σ.relators

/-- Every side-identification word is trivial in the relator quotient. -/
@[simp]
theorem relatorQuotient_sideRelator (i : Fin n) :
    PresentedGroup.mk σ.relators (σ.sideRelator i) = 1 :=
  PresentedGroup.one_of_mem (σ.sideRelator_mem_relators i)

/-- Paired sides give inverse generators in the relator quotient. -/
@[simp]
theorem relatorQuotient_of_pair (i : Fin n) :
    (PresentedGroup.of (σ.pair i) : σ.RelatorQuotient) = (PresentedGroup.of i)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  simpa only [sideRelator_def, map_mul, PresentedGroup.of] using
    σ.relatorQuotient_sideRelator i

/-- A finite-vertex cycle word has order dividing that of its cycle transformation in the
relator quotient. -/
@[simp]
theorem relatorQuotient_cycleWord_pow {j : Fin n} {z : ℍ}
    (hj : P.vertex j = .inl z) :
    (PresentedGroup.mk σ.relators (σ.cycleWord j)) ^ orderOf (σ.cycleMap j) = 1 := by
  rw [← map_pow]
  exact PresentedGroup.one_of_mem (σ.cycleWord_pow_mem_relators hj)

/-- Evaluation of the side generators as elements of a subgroup containing all the pairing
transformations. -/
def generatorsIn {Γ : Subgroup PSL(2, ℝ)} (hmap : ∀ i, σ.map i ∈ Γ) (i : Fin n) : Γ :=
  ⟨σ.map i, hmap i⟩

@[simp]
theorem coe_generatorsIn {Γ : Subgroup PSL(2, ℝ)} (hmap : ∀ i, σ.map i ∈ Γ)
    (i : Fin n) : (σ.generatorsIn hmap i : PSL(2, ℝ)) = σ.map i :=
  by simp [generatorsIn]

/-- Evaluation of side words in a subgroup agrees with evaluation in `PSL(2, ℝ)`. -/
theorem subtype_comp_lift_generatorsIn {Γ : Subgroup PSL(2, ℝ)}
    (hmap : ∀ i, σ.map i ∈ Γ) :
    Γ.subtype.comp (FreeGroup.lift (σ.generatorsIn hmap)) = σ.pairingHom := by
  ext i
  simp

/-- The side-pairing relators hold in every subgroup containing the pairing transformations. -/
theorem lift_generatorsIn_eq_one_of_mem_relators {Γ : Subgroup PSL(2, ℝ)}
    (hmap : ∀ i, σ.map i ∈ Γ) {w : FreeGroup (Fin n)} (hw : w ∈ σ.relators) :
    FreeGroup.lift (σ.generatorsIn hmap) w = 1 := by
  apply Γ.subtype_injective
  rw [← MonoidHom.comp_apply, σ.subtype_comp_lift_generatorsIn hmap]
  exact σ.pairingHom_eq_one_of_mem_relators hw

/-- Evaluate the side-pairing relator quotient in a subgroup containing the pairing maps. -/
def relatorQuotientTo {Γ : Subgroup PSL(2, ℝ)} (hmap : ∀ i, σ.map i ∈ Γ) :
    σ.RelatorQuotient →* Γ :=
  PresentedGroup.toGroup (fun _ hw ↦ σ.lift_generatorsIn_eq_one_of_mem_relators hmap hw)

/-- Evaluation of a side generator in the relator quotient is its pairing transformation. -/
@[simp]
theorem relatorQuotientTo_of {Γ : Subgroup PSL(2, ℝ)} (hmap : ∀ i, σ.map i ∈ Γ)
    (i : Fin n) : σ.relatorQuotientTo hmap (PresentedGroup.of i) = σ.generatorsIn hmap i :=
  PresentedGroup.toGroup.of _

/-- Evaluation after passing to the relator quotient agrees with evaluation of side words. -/
@[simp]
theorem relatorQuotientTo_mk {Γ : Subgroup PSL(2, ℝ)} (hmap : ∀ i, σ.map i ∈ Γ)
    (w : FreeGroup (Fin n)) :
    σ.relatorQuotientTo hmap (PresentedGroup.mk σ.relators w) =
      FreeGroup.lift (σ.generatorsIn hmap) w := by
  exact FreeGroup.lift_unique
    ((σ.relatorQuotientTo hmap).comp (PresentedGroup.mk σ.relators))
    (fun i => by simpa [PresentedGroup.of] using σ.relatorQuotientTo_of hmap i)

/-- The cycle word at a finite vertex has exactly the same order in the relator quotient as
its transformation. Relations at other sides and vertices cannot shorten this order. -/
theorem orderOf_relatorQuotient_cycleWord {j : Fin n} {z : ℍ}
    (hj : P.vertex j = .inl z) :
    orderOf (PresentedGroup.mk σ.relators (σ.cycleWord j)) =
      orderOf (σ.cycleMap j) := by
  let hmap : ∀ i, σ.map i ∈ (⊤ : Subgroup PSL(2, ℝ)) := fun _ => Subgroup.mem_top _
  have heval :
      ((σ.relatorQuotientTo hmap) (PresentedGroup.mk σ.relators (σ.cycleWord j)) :
        PSL(2, ℝ)) = σ.cycleMap j := by
    rw [σ.relatorQuotientTo_mk]
    have h := congrArg (fun f : FreeGroup (Fin n) →* PSL(2, ℝ) ↦ f (σ.cycleWord j))
      (σ.subtype_comp_lift_generatorsIn hmap)
    simpa using h
  apply Nat.dvd_antisymm
  · exact orderOf_dvd_iff_pow_eq_one.mpr (σ.relatorQuotient_cycleWord_pow hj)
  · have h := orderOf_map_dvd (σ.relatorQuotientTo hmap)
      (PresentedGroup.mk σ.relators (σ.cycleWord j))
    have h' : orderOf
        (((σ.relatorQuotientTo hmap) (PresentedGroup.mk σ.relators (σ.cycleWord j))) :
          PSL(2, ℝ)) ∣
        orderOf (PresentedGroup.mk σ.relators (σ.cycleWord j)) := by
      simpa only [Subgroup.orderOf_coe] using h
    rwa [heval] at h'

/-- The relator quotient maps onto the group of a locally finite fundamental polygon. -/
theorem relatorQuotientTo_surjective {Γ : Subgroup PSL(2, ℝ)}
    (hmap : ∀ i, σ.map i ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier)) :
    Function.Surjective (σ.relatorQuotientTo hmap) := by
  have hclosure : Subgroup.closure (range (σ.generatorsIn hmap)) = ⊤ := by
    apply Subgroup.map_subtype_inj.mp
    rw [MonoidHom.map_closure, Subgroup.map_top, Γ.range_subtype]
    have hrange : Γ.subtype '' range (σ.generatorsIn hmap) = range σ.map := by
      ext x
      simp
    rw [hrange]
    exact σ.closure_range_map_eq hmap hlf hdisj
  have hlift : Function.Surjective (FreeGroup.lift (σ.generatorsIn hmap)) :=
    FreeGroup.lift_surjective_iff_closure_range_eq_top.mpr hclosure
  intro γ
  obtain ⟨w, hw⟩ := hlift γ
  exact ⟨PresentedGroup.mk σ.relators w, by simpa using hw⟩

/-! ### Injectivity of the evaluation -/

/-- If `d` steps along the cycle of a finite vertex compose to the identity, then the
corresponding partial cycle word is trivial in the relator quotient. -/
theorem relatorQuotient_partialCycleWord_eq_one {j : Fin n} {z : ℍ} (hj : P.vertex j = .inl z)
    {d : ℕ} (hd : σ.partialCycleMap j d = 1) :
    PresentedGroup.mk σ.relators (σ.partialCycleWord j d) = 1 := by
  have hper : σ.next^[d] j = j := P.vertex_injective <| by
    rw [← σ.partialCycleMap_smul_vertex, hd, one_smul]
  obtain ⟨c, rfl⟩ := Function.IsPeriodicPt.minimalPeriod_dvd hper
  rw [← cycleLength_def, mul_comm] at hd ⊢
  rw [partialCycleMap_mul_cycleLength] at hd
  obtain ⟨e, rfl⟩ := orderOf_dvd_of_pow_eq_one hd
  rw [partialCycleWord_mul_cycleLength, map_pow, pow_mul, σ.relatorQuotient_cycleWord_pow hj,
    one_pow]

/-- Two partial cycle words at a finite vertex with the same transformation are equal in the
relator quotient. -/
theorem relatorQuotient_partialCycleWord_eq_of_partialCycleMap_eq {j : Fin n} {z : ℍ}
    (hj : P.vertex j = .inl z) {a b : ℕ}
    (hab : σ.partialCycleMap j a = σ.partialCycleMap j b) :
    PresentedGroup.mk σ.relators (σ.partialCycleWord j a) =
      PresentedGroup.mk σ.relators (σ.partialCycleWord j b) := by
  wlog h : a ≤ b generalizing a b
  · exact (this hab.symm (le_of_not_ge h)).symm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have hk : P.vertex (σ.next^[a] j) = .inl (σ.partialCycleMap j a • z) := by
    rw [← σ.partialCycleMap_smul_vertex, hj, Sum.smul_inl]
  rw [partialCycleMap_add, right_eq_mul] at hab
  rw [partialCycleWord_add, map_mul, σ.relatorQuotient_partialCycleWord_eq_one hk hab, one_mul]

/-- A side-pairing map which is an inverse partial cycle product at a finite vertex has the
inverse partial cycle word as its side generator. The vertex is an endpoint of the side met by
the translate, so the cycle has made one step forwards or backwards. -/
private theorem of_eq_inv_mk_partialCycleWord {i j : Fin n} {z : ℍ} (hj : P.vertex j = .inl z)
    {m : ℕ} (h : σ.map i = (σ.partialCycleMap j m)⁻¹) :
    PresentedGroup.of i = (PresentedGroup.mk σ.relators (σ.partialCycleWord j m))⁻¹ := by
  have hzP : z ∈ P.carrier := P.vertex_mem_carrier hj
  have hzi : z ∈ σ.map i • P.carrier := by
    rw [h, mem_smul_set_iff_inv_smul_mem, inv_inv]
    exact P.vertex_mem_carrier (by rw [← σ.partialCycleMap_smul_vertex, hj, Sum.smul_inl])
  have hside : z ∈ P.side (σ.pair i) := P.carrier_inter_range_sideGeodesic _ ▸
    ⟨hzP, σ.inter_smul_carrier_subset_range_sideGeodesic i ⟨hzP, hzi⟩⟩
  rcases P.eq_or_eq_add_one_of_vertex_eq_inl_of_mem_side hj hside with rfl | rfl
  · -- the vertex starts side `pair i`, whose map is the first step of the cycle
    have h1 : σ.partialCycleMap (σ.pair i) 1 = (σ.map i)⁻¹ := by simp [partialCycleMap_succ]
    have hm1 : σ.partialCycleMap (σ.pair i) m = σ.partialCycleMap (σ.pair i) 1 := by
      rw [h1, h, inv_inv]
    rw [σ.relatorQuotient_partialCycleWord_eq_of_partialCycleMap_eq hj hm1, partialCycleWord_succ,
      Function.iterate_zero_apply, partialCycleWord_zero, mul_one, eq_inv_iff_mul_eq_one]
    simpa [sideRelator_def, PresentedGroup.of] using σ.relatorQuotient_sideRelator (σ.pair i)
  · -- the vertex ends side `pair i`, so the map of side `i` closes the cycle at `vertex i`
    have hi : P.vertex i = .inl ((σ.map i)⁻¹ • z) := by
      rw [← Sum.smul_inl, ← hj, ← σ.map_smul_vertex, inv_smul_smul]
    have h1 : σ.partialCycleMap i (m + 1) = 1 := by
      rw [partialCycleMap_succ', next_apply, h, mul_inv_cancel]
    have h2 := σ.relatorQuotient_partialCycleWord_eq_one hi h1
    rw [partialCycleWord_succ', next_apply, map_mul] at h2
    exact eq_inv_of_mul_eq_one_right h2

variable {Γ : Subgroup PSL(2, ℝ)}

/-- Two inverse partial cycle products at finite vertices which give the same element of `Γ`
have the same word in the relator quotient. If the vertices differ, the common translate
contains both, so they are the endpoints of one side and the translate is its side neighbour. -/
private theorem mk_partialCycleWord_eq_of_partialCycleMap_eq (hmap : ∀ i, σ.map i ∈ Γ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier))
    {j j' : Fin n} {z z' : ℍ} (hj : P.vertex j = .inl z) (hj' : P.vertex j' = .inl z')
    {m m' : ℕ} (h : σ.partialCycleMap j m = σ.partialCycleMap j' m') :
    PresentedGroup.mk σ.relators (σ.partialCycleWord j m) =
      PresentedGroup.mk σ.relators (σ.partialCycleWord j' m') := by
  obtain rfl | hjj' := eq_or_ne j j'
  · exact σ.relatorQuotient_partialCycleWord_eq_of_partialCycleMap_eq hj h
  by_cases h1 : σ.partialCycleMap j m = 1
  · rw [σ.relatorQuotient_partialCycleWord_eq_one hj h1,
      σ.relatorQuotient_partialCycleWord_eq_one hj' (h ▸ h1)]
  have hgΓ : (σ.partialCycleMap j m)⁻¹ ∈ Γ := Γ.inv_mem (σ.partialCycleMap_mem hmap j m)
  have hmem {k : Fin n} {w : ℍ} (hk : P.vertex k = .inl w) (l : ℕ) :
      w ∈ (σ.partialCycleMap k l)⁻¹ • P.carrier := by
    rw [mem_smul_set_iff_inv_smul_mem, inv_inv]
    exact P.vertex_mem_carrier (by rw [← σ.partialCycleMap_smul_vertex, hk, Sum.smul_inl])
  have hzz' : z ≠ z' := fun he ↦ hjj' (P.vertex_injective (by rw [hj, hj', he]))
  -- the common translate is convex and contains both vertices
  have hseg : geodesicSegment z z' ⊆ (σ.partialCycleMap j m)⁻¹ • P.carrier := by
    rw [← carrier_smul]
    exact geodesicSegment_subset_carrier _ (by rw [carrier_smul]; exact hmem hj m)
      (by rw [carrier_smul, h]; exact hmem hj' m')
  -- the two vertices lie on a common side, since the translate misses the interior of `P`
  obtain ⟨k, hzk, hz'k⟩ : ∃ k, z ∈ P.side k ∧ z' ∈ P.side k := by
    by_contra! hside
    obtain ⟨v, hvseg, hvint⟩ := P.geodesicSegment_inter_interior_carrier_nonempty
      (P.vertex_mem_carrier hj) (P.vertex_mem_carrier hj') hzz' hside
    exact h1 (inv_eq_one.1 (P.eq_of_smul_interior_inter_smul_carrier_nonempty hdisj Γ.one_mem
      hgΓ ⟨v, by simpa using hvint, hseg hvseg⟩).symm)
  have hsidek : P.side k ⊆ (σ.partialCycleMap j m)⁻¹ • P.carrier := by
    rcases P.eq_or_eq_add_one_of_vertex_eq_inl_of_mem_side hj hzk with rfl | rfl <;>
      rcases P.eq_or_eq_add_one_of_vertex_eq_inl_of_mem_side hj' hz'k with rfl | rfl
    · exact absurd rfl hjj'
    · rwa [side_def, hj, hj', extGeodesicSegment_inl_inl]
    · rwa [side_def, hj, hj', extGeodesicSegment_inl_inl, geodesicSegment_comm]
    · exact absurd rfl hjj'
  -- so the translate is the side neighbour across side `k`
  obtain ⟨w, hw, hwp, hwq⟩ := P.exists_mem_side_ne_endpoints k
  have hgk : σ.map (σ.pair k) = (σ.partialCycleMap j m)⁻¹ := by
    have hwg := mem_smul_set_iff_inv_smul_mem.1 (hsidek hw)
    exact ((σ.eq_one_or_eq_map_pair_of_smul_mem_side (hmap _) hdisj hgΓ hwg hw hwp hwq
      (smul_inv_smul _ w)).resolve_left (by simpa using h1)).symm
  rw [← inv_inj, ← σ.of_eq_inv_mk_partialCycleWord hj hgk,
    σ.of_eq_inv_mk_partialCycleWord hj' (h ▸ hgk)]

/-- `x` is a side word of `g` when `g` is the identity and `x = 1`, `g` is the map of a side
and `x` its generator, or `g` is an inverse partial cycle product at a finite vertex and `x`
the inverse of the partial cycle word. -/
private def IsSideWord (g : PSL(2, ℝ)) (x : σ.RelatorQuotient) : Prop :=
  (g = 1 ∧ x = 1) ∨ (∃ i, g = σ.map i ∧ x = PresentedGroup.of i) ∨
    ∃ (j : Fin n) (z : ℍ) (m : ℕ), P.vertex j = .inl z ∧ g = (σ.partialCycleMap j m)⁻¹ ∧
      x = (PresentedGroup.mk σ.relators (σ.partialCycleWord j m))⁻¹

/-- A transformation has at most one side word. -/
private theorem isSideWord_unique (hmap : ∀ i, σ.map i ∈ Γ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier))
    {x y : σ.RelatorQuotient} {g : PSL(2, ℝ)} (hx : σ.IsSideWord g x) (hy : σ.IsSideWord g y) :
    x = y := by
  rcases hx with ⟨rfl, rfl⟩ | ⟨i, rfl, rfl⟩ | ⟨j, z, m, hj, rfl, rfl⟩ <;>
    rcases hy with ⟨h, rfl⟩ | ⟨i', h, rfl⟩ | ⟨j', z', m', hj', h, rfl⟩
  · rfl
  · exact absurd h.symm (σ.map_ne_one i')
  · rw [σ.relatorQuotient_partialCycleWord_eq_one hj' (inv_eq_one.1 h.symm), inv_one]
  · exact absurd h (σ.map_ne_one i)
  · rw [σ.map_injective h]
  · exact σ.of_eq_inv_mk_partialCycleWord hj' h
  · rw [σ.relatorQuotient_partialCycleWord_eq_one hj (inv_eq_one.1 h), inv_one]
  · exact (σ.of_eq_inv_mk_partialCycleWord hj h.symm).symm
  · rw [σ.mk_partialCycleWord_eq_of_partialCycleMap_eq hmap hdisj hj hj' (inv_injective h)]

/-- The side word of `g`, when it has one. -/
private def sideWord (g : PSL(2, ℝ)) : σ.RelatorQuotient :=
  open Classical in if h : ∃ x, σ.IsSideWord g x then h.choose else 1

/-- The side word of a transformation is any of its side words. -/
private theorem sideWord_eq (hmap : ∀ i, σ.map i ∈ Γ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier))
    {g : PSL(2, ℝ)} {x : σ.RelatorQuotient} (hx : σ.IsSideWord g x) : σ.sideWord g = x := by
  have h : ∃ x, σ.IsSideWord g x := ⟨x, hx⟩
  simp only [sideWord, h, dite_true]
  exact σ.isSideWord_unique hmap hdisj h.choose_spec hx

/-- The Macbeath relation of three tiles around a finite vertex: the side words of the inverse
partial cycle products are compatible with multiplication. -/
private theorem sideWord_inv_partialCycleMap_mul (hmap : ∀ i, σ.map i ∈ Γ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier))
    {j : Fin n} {z : ℍ} (hj : P.vertex j = .inl z) {a : ℕ}
    (ha : a < orderOf (σ.cycleMap j) * σ.cycleLength j) (b : ℕ) :
    σ.sideWord (σ.partialCycleMap j a)⁻¹ *
        σ.sideWord (σ.partialCycleMap j a * (σ.partialCycleMap j b)⁻¹) =
      σ.sideWord (σ.partialCycleMap j b)⁻¹ := by
  set N := orderOf (σ.cycleMap j) * σ.cycleLength j with hN
  -- a full turn around the vertex returns to the identity
  have hN1 : σ.partialCycleMap j N = 1 := by
    rw [hN, partialCycleMap_mul_cycleLength, pow_orderOf_eq_one]
  have hper : σ.next^[N] j = j := P.vertex_injective <| by
    rw [← σ.partialCycleMap_smul_vertex, hN1, one_smul]
  have hNb : σ.partialCycleMap j (N + b) = σ.partialCycleMap j b := by
    rw [partialCycleMap_add, hper, hN1, mul_one]
  have hk : P.vertex (σ.next^[a] j) = .inl (σ.partialCycleMap j a • z) := by
    rw [← σ.partialCycleMap_smul_vertex, hj, Sum.smul_inl]
  obtain ⟨c, hc⟩ : ∃ c, N + b = a + c := ⟨N + b - a, by omega⟩
  have ht : σ.partialCycleMap j a * (σ.partialCycleMap j b)⁻¹ =
      (σ.partialCycleMap (σ.next^[a] j) c)⁻¹ := by
    rw [← hNb, hc, partialCycleMap_add, mul_inv_rev, mul_inv_cancel_left]
  rw [ht, σ.sideWord_eq hmap hdisj (Or.inr (Or.inr ⟨j, z, a, hj, rfl, rfl⟩)),
    σ.sideWord_eq hmap hdisj (Or.inr (Or.inr ⟨_, _, c, hk, rfl, rfl⟩)),
    σ.sideWord_eq hmap hdisj (Or.inr (Or.inr ⟨j, z, b, hj, rfl, rfl⟩)), ← mul_inv_rev, ← map_mul,
    ← partialCycleWord_add, ← hc,
    σ.relatorQuotient_partialCycleWord_eq_of_partialCycleMap_eq hj hNb]

/-- The side word of the identity is trivial. -/
private theorem sideWord_one (hmap : ∀ i, σ.map i ∈ Γ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier)) :
    σ.sideWord 1 = 1 :=
  σ.sideWord_eq hmap hdisj (Or.inl ⟨rfl, rfl⟩)

/-- The side words of a tile meeting the polygon and of its inverse are inverse. -/
private theorem sideWord_mul_sideWord_inv (hmap : ∀ i, σ.map i ∈ Γ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier))
    {g : PSL(2, ℝ)} (hg : g ∈ Γ) (hmeet : (P.carrier ∩ g • P.carrier).Nonempty) :
    σ.sideWord g * σ.sideWord g⁻¹ = 1 := by
  rcases (σ.inter_smul_carrier_nonempty_iff hmap hdisj hg).1 hmeet with
    rfl | ⟨i, rfl⟩ | ⟨j, z, hj, m, hm, rfl⟩
  · rw [inv_one, σ.sideWord_one hmap hdisj, one_mul]
  · rw [← map_pair, σ.sideWord_eq hmap hdisj (Or.inr (Or.inl ⟨i, rfl, rfl⟩)),
      σ.sideWord_eq hmap hdisj (Or.inr (Or.inl ⟨_, rfl, rfl⟩))]
    simpa [sideRelator_def, PresentedGroup.of] using σ.relatorQuotient_sideRelator (σ.pair i)
  · simpa [σ.sideWord_one hmap hdisj] using σ.sideWord_inv_partialCycleMap_mul hmap hdisj hj hm 0

/-- The Macbeath relations hold between side words: if the polygon meets `s • P` and
`(s * t) • P` at a common point, the side word of `s * t` is the product of those of `s`
and `t`. -/
private theorem sideWord_mul_sideWord (hmap : ∀ i, σ.map i ∈ Γ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier))
    {s t : PSL(2, ℝ)} (hs : s ∈ Γ) (ht : t ∈ Γ) (hs' : (P.carrier ∩ s • P.carrier).Nonempty)
    (hmeet : (P.carrier ∩ s • P.carrier ∩ (s * t) • P.carrier).Nonempty) :
    σ.sideWord s * σ.sideWord t = σ.sideWord (s * t) := by
  by_cases hs1 : s = 1
  · rw [hs1, σ.sideWord_one hmap hdisj, one_mul, one_mul]
  by_cases hst : s * t = 1
  · rw [hst, σ.sideWord_one hmap hdisj, eq_inv_of_mul_eq_one_right hst,
      σ.sideWord_mul_sideWord_inv hmap hdisj hs hs']
  by_cases hts : s * t = s
  · rw [mul_eq_left.1 hts, mul_one, σ.sideWord_one hmap hdisj, mul_one]
  -- three distinct tiles meet only at a finite vertex, where they are partial cycle tiles
  obtain ⟨x, ⟨hxP, hxs⟩, hxu⟩ := hmeet
  have hu : s * t ∈ Γ := Γ.mul_mem hs ht
  obtain ⟨j, hj⟩ := σ.exists_vertex_of_mem_carrier_of_mem_two_smul_carrier hmap hdisj hs hu hs1
    hst (Ne.symm hts) hxP hxs hxu
  obtain ⟨a, ha, hsa⟩ :=
    (σ.mem_smul_carrier_iff_exists_inv_partialCycleMap_eq hj hmap hdisj hs).1 hxs
  obtain ⟨b, -, hub⟩ :=
    (σ.mem_smul_carrier_iff_exists_inv_partialCycleMap_eq hj hmap hdisj hu).1 hxu
  have htab : t = σ.partialCycleMap j a * (σ.partialCycleMap j b)⁻¹ := by
    rw [hub, ← hsa, mul_inv_cancel_left]
  rw [← hub, htab, ← hsa]
  exact σ.sideWord_inv_partialCycleMap_mul hmap hdisj hj ha b

/-- The Macbeath relations of the polygon are killed by the side words. -/
private theorem lift_sideWord_eq_one_of_mem_macbeathRels (hmap : ∀ i, σ.map i ∈ Γ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier)) :
    ∀ r ∈ macbeathRels Γ P.carrier,
      FreeGroup.lift (fun s : macbeathGenerators Γ P.carrier ↦ σ.sideWord ((s : Γ) : PSL(2, ℝ)))
        r = 1 := by
  intro r hr
  obtain ⟨s, t, u, hu, hmeet, rfl⟩ := mem_macbeathRels.1 hr
  have hs := s.2
  rw [mem_macbeathGenerators, Set.subtype_smul_set] at hs
  rw [Set.subtype_smul_set, Set.subtype_smul_set, hu, Subgroup.coe_mul] at hmeet
  rw [map_mul, map_mul, map_inv, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of,
    FreeGroup.lift_apply_of, mul_inv_eq_one, hu, Subgroup.coe_mul]
  exact σ.sideWord_mul_sideWord hmap hdisj (s : Γ).2 (t : Γ).2 hs hmeet

/-- **Poincaré's presentation theorem.** For a locally finite fundamental polygon, every word in
the side generators evaluating to the identity is a consequence of the side relations and the
finite-vertex cycle relations. -/
theorem relatorQuotientTo_injective (hmap : ∀ i, σ.map i ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier)) :
    Function.Injective (σ.relatorQuotientTo hmap) := by
  -- invert the evaluation through Macbeath's presentation by the tiles meeting `P`
  let e := MulEquiv.ofBijective _ (σ.macbeathHom_bijective hmap hlf)
  let ψ : Γ →* σ.RelatorQuotient :=
    (PresentedGroup.toGroup (σ.lift_sideWord_eq_one_of_mem_macbeathRels hmap hdisj)).comp
      e.symm.toMonoidHom
  have hψ : ψ.comp (σ.relatorQuotientTo hmap) = MonoidHom.id _ := by
    refine PresentedGroup.ext fun i ↦ ?_
    have hgen : σ.generatorsIn hmap i ∈ macbeathGenerators Γ P.carrier := by
      rw [mem_macbeathGenerators, Set.subtype_smul_set, coe_generatorsIn]
      exact (σ.inter_smul_carrier_nonempty_iff hmap hdisj (hmap i)).2 (Or.inr (Or.inl ⟨i, rfl⟩))
    have he : e.symm (σ.generatorsIn hmap i) = PresentedGroup.of ⟨_, hgen⟩ :=
      e.symm_apply_eq.2 (by simp only [e, MulEquiv.ofBijective_apply, macbeathHom_of])
    simp only [ψ, MonoidHom.comp_apply, relatorQuotientTo_of, MulEquiv.coe_toMonoidHom, he,
      PresentedGroup.toGroup.of, coe_generatorsIn, MonoidHom.id_apply]
    exact σ.sideWord_eq hmap hdisj (Or.inr (Or.inl ⟨i, rfl, rfl⟩))
  exact Function.LeftInverse.injective (g := ψ) fun x ↦ DFunLike.congr_fun hψ x

/-- **Poincaré's presentation theorem.** The group of a locally finite fundamental polygon is
presented by the side generators, the side relations, and the finite-vertex cycle relations. -/
theorem relatorQuotientTo_bijective (hmap : ∀ i, σ.map i ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier)) :
    Function.Bijective (σ.relatorQuotientTo hmap) :=
  ⟨σ.relatorQuotientTo_injective hmap hlf hdisj, σ.relatorQuotientTo_surjective hmap hlf hdisj⟩

/-- **Poincaré's presentation theorem**, as a description of the relations: the words in the
side generators evaluating to the identity in the group of a locally finite fundamental polygon
form the normal closure of the side and finite-vertex cycle relators. -/
theorem ker_lift_generatorsIn_eq_normalClosure_relators (hmap : ∀ i, σ.map i ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier)) :
    (FreeGroup.lift (σ.generatorsIn hmap)).ker = Subgroup.normalClosure σ.relators := by
  ext w
  rw [MonoidHom.mem_ker, ← relatorQuotientTo_mk,
    (injective_iff_map_eq_one' _).1 (σ.relatorQuotientTo_injective hmap hlf hdisj),
    PresentedGroup.mk_eq_one_iff]

end TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing
