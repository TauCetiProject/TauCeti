/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Selmer.Isogeny.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Reciprocity
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SelmerStructure.Comparison
import TauCeti.Algebra.Group.Pi.Pairing
import TauCeti.Algebra.Group.Subgroup.Pi
import TauCeti.Algebra.Module.ZMod.Annihilator
import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Finiteness
import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Selmer.Isogeny.Reciprocity
import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Orthogonality
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Degree
import TauCeti.GroupTheory.Index.Comap

/-!
# The orthogonality bound for the Selmer groups of an isogeny and its dual

Let `φ : E₁ → E₂` be an isogeny of elliptic curves over a number field `K`, with dual `φ̂`, and let
`S` be a finite set of finite places of `K`. Write `Sel_φ ⊆ H¹(K, E₁[φ])` and
`Sel_φ̂ ⊆ H¹(K, E₂[φ̂])` for the two Selmer groups, `Sel_φ^S` for the `φ`-Selmer group relaxed at
`S` (no local condition at the places of `S`) and `Sel_φ̂,S` for the `φ̂`-Selmer group strict at
`S` (zero local condition there). This file proves

`[Sel_φ^S : Sel_φ] · [Sel_φ̂ : Sel_φ̂,S] ≤ ∏_{v ∈ S} [H¹(K_v, E₁[φ]) : H¹_φ(K_v)]`

(`TauCeti.Isogeny.relIndex_selmerGroup_relaxedAt_mul_relIndex_strictAt_dual_le`), where
`H¹_φ(K_v)` is the local condition of `φ` at `v`. The groups `H¹(K_v, E₁[φ])` for `v ∈ S` are
finite, since `K_v` is a finite extension of `ℚ_p`
(`TauCeti.Isogeny.finite_H1_kerCoeff_adicCompletion`).

The proof is the orthogonality half of global duality. The local Tate pairings
`H¹(K_v, E₁[φ]) × H¹(K_v, E₂[φ̂]) → ℤ/deg φ` at the places of `S` add up to a perfect pairing of
the products (`AddMonoidHom.piPairing_bijective`). Under it, the classes of `∏_v H¹_φ(K_v)` and the
localisations of `Sel_φ^S` are orthogonal to the localisations of `Sel_φ̂`: the former by local
orthogonality of the Selmer conditions, the latter by global reciprocity; see
`sum_ringEquivCongr_localTateKerWeilPairing_eq_zero_of_mem_selmerGroup_relaxedAt_of_mem_selmerGroup`
in `TauCeti.Isogeny`. Counting orthogonal subgroups of a perfect pairing
(`AddMonoidHom.natCard_mul_natCard_le_zmod`) gives the bound.

Poitou–Tate duality gives equality: the image of `Sel_φ^S` in `∏_v H¹(K_v, E₁[φ]) / H¹_φ(K_v)` is
the exact annihilator of the image of `Sel_φ̂`. That is the comparison of Selmer groups in
Cassels' formula for `#Sel_φ / #Sel_φ̂`; the inequality here is the half that reciprocity alone
gives.

## Main results

* `TauCeti.Isogeny.relIndex_selmerGroup_relaxedAt_mul_relIndex_strictAt_dual_le`: the
  orthogonality bound.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, second edition, I, §4.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. reine angew. Math. 217 (1965), 180–199.
* K. Rubin, *Euler Systems*, Annals of Mathematics Studies 147, Princeton University Press,
  2000, I.7.
-/

public section

noncomputable section

namespace TauCeti.Isogeny

open WeierstrassCurve TauCeti.ContCohomology Hom
open IsDedekindDomain _root_.NumberField

variable {K : Type} [Field K] [NumberField K] {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic]
  [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine)
  (τ : ∀ v : GlobalNumberFields.Place K,
    SeparableClosure K →ₐ[K] SeparableClosure v.Completion)

/-! ### The orthogonality bound

At a finite place `v`, the Selmer structures localise to `GlobalNumberFields.Place.Completion
(.inl v)`, which is `v.adicCompletion K` by definition, with the same field and `K`-algebra
structures. The local pairings and global reciprocity are stated over `v.adicCompletion K`; the
proofs below pass between the two descriptions of the same local cohomology group by this
definitional identification. -/

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- Localisation of `H¹(K, E₁[φ])` at the places of `S`. -/
private def locRes :
    H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff →+
      ∀ v : S, H1 (AbsoluteGaloisGroup ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K))
        (ofIsogeny (φ.baseChange ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K))).KerCoeff :=
  AddMonoidHom.pi fun v ↦ φ.kerRes (L := (v : HeightOneSpectrum (𝓞 K)).adicCompletion K)
    (τ (.inl v))

/-- Localisation of `H¹(K, E₂[φ̂])` at the places of `S`, into the kernels of the duals of the
base changes of `φ`. -/
private def locDualRes :
    H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff →+
      ∀ v : S, H1 (AbsoluteGaloisGroup ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K))
        (ofIsogeny (φ.baseChange ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)).dual).KerCoeff :=
  AddMonoidHom.pi fun v ↦ φ.dualKerRes (L := (v : HeightOneSpectrum (𝓞 K)).adicCompletion K)
    (τ (.inl v))

/-- The product of the local conditions of `φ` at the places of `S`. -/
private def localConditions :
    AddSubgroup (∀ v : S, H1 (AbsoluteGaloisGroup ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K))
      (ofIsogeny (φ.baseChange ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K))).KerCoeff) :=
  AddSubgroup.pi Set.univ fun v ↦
    (φ.baseChange ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)).localKummerCondition

/-- The orthogonal subgroups of the product pairing have orders multiplying to at most the order
of the product of the local cohomology groups. -/
private theorem natCard_sup_mul_natCard_map_le :
    Nat.card (localConditions φ S ⊔
        ((φ.selmerStructure τ).relaxedAt (Sum.inl '' S)).selmerGroup.map (locRes φ τ S) :) *
      Nat.card ((φ.dual.selmerGroup τ).map (locDualRes φ τ S)) ≤
    Nat.card (∀ v : S, H1 (AbsoluteGaloisGroup ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K))
      (ofIsogeny (φ.baseChange ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K))).KerCoeff) := by
  have : NeZero φ.degree := ⟨φ.degree_ne_zero⟩
  let e (v : HeightOneSpectrum (𝓞 K)) :=
    ZMod.ringEquivCongr (degree_baseChange φ (K := v.adicCompletion K))
  let pairing (v : S) :=
    (AddMonoidHom.compHom (e v.val).toAddMonoidHom).comp
      ((φ.baseChange (v.val.adicCompletion K)).localTateKerWeilPairing
        (isUnit_natCast_of_ne_zero ℚ (φ.baseChange (v.val.adicCompletion K)).degree_ne_zero))
  refine (AddMonoidHom.piPairing pairing).natCard_mul_natCard_le_zmod
    (AddMonoidHom.piPairing_bijective _ fun v ↦ ?_)
    (fun y ↦ funext fun v ↦ nsmul_H1_eq_zero (fun Q ↦ ?_) (y v)) ?_
  · change Function.Bijective (AddMonoidHom.compHom (e v.val).toAddMonoidHom ∘ _)
    refine (Function.bijective_iff_has_inverse.mpr
      ⟨AddMonoidHom.compHom (e v.val).symm.toAddMonoidHom, fun f ↦ ?_, fun f ↦ ?_⟩).comp
      ((φ.baseChange (v.val.adicCompletion K)).localTateKerWeilPairing_bijective _) <;>
    ext <;> simp [e]
  · simpa only [degree_dual, degree_baseChange] using degree_nsmul_kerCoeff_eq_zero
      (φ.baseChange ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)).dual Q
  · intro x hx y hy
    obtain ⟨p, hp, l, ⟨c, hc, rfl⟩, rfl⟩ := AddSubgroup.mem_sup.mp hx
    obtain ⟨d, hd, rfl⟩ := hy
    rw [_root_.map_add, AddMonoidHom.add_apply, AddMonoidHom.piPairing_apply,
      AddMonoidHom.piPairing_apply, Finset.sum_eq_zero fun v _ ↦ ?_, zero_add]
    · dsimp only [pairing, e, AddMonoidHom.comp_apply, AddMonoidHom.compHom_apply_apply,
        locRes, locDualRes, AddMonoidHom.pi_apply]
      exact (Finset.sum_coe_sort S _).trans (
  sum_ringEquivCongr_localTateKerWeilPairing_eq_zero_of_mem_selmerGroup_relaxedAt_of_mem_selmerGroup
        φ τ S hc hd)
    · have hd' :=
        (φ.dual.mem_selmerGroup_iff_forall_kerRes_mem_localKummerCondition τ).mp hd (.inl v)
      rw [mem_localKummerCondition_iff] at hd'
      simp only [pairing, e, AddMonoidHom.comp_apply, AddMonoidHom.compHom_apply_apply,
        locDualRes, AddMonoidHom.pi_apply, localTateKerWeilPairing_apply]
      rw [kerH1WeilPairing_eq_zero_of_mem_localKummerCondition _ _ (hp v (Set.mem_univ v)) (by
        rw [mem_localKummerCondition_iff, explicitCoeff1_kerCoeffIncl_dualKerRes]
        exact hd'), map_zero, map_zero, map_zero]

/-- The order of the subgroup generated by the local conditions and the localisations of the
relaxed Selmer group is `#∏_v H¹_φ(K_v) · [Sel_φ^S : Sel_φ]`. -/
private theorem natCard_sup :
    Nat.card (localConditions φ S ⊔
        ((φ.selmerStructure τ).relaxedAt (Sum.inl '' S)).selmerGroup.map (locRes φ τ S) :) =
      (φ.selmerGroup τ).relIndex ((φ.selmerStructure τ).relaxedAt (Sum.inl '' S)).selmerGroup *
        Nat.card (localConditions φ S) := by
  -- After `natCard_sup_map`, it remains to show that inside the relaxed Selmer group the
  -- preimage of the local conditions is `Sel_φ`.
  rw [AddSubgroup.natCard_sup_map, ← AddSubgroup.inf_relIndex_right,
    ← AddSubgroup.inf_relIndex_right (φ.selmerGroup τ)]
  congr 2
  ext c
  rw [selmerGroup_def, AddSubgroup.mem_inf, AddSubgroup.mem_inf]
  refine and_congr_left fun hc ↦ ?_
  rw [SelmerStructure.mem_selmerGroup_relaxedAt_iff] at hc
  simp only [AddSubgroup.mem_comap, localConditions, AddSubgroup.mem_pi, Set.mem_univ,
    forall_const, locRes, AddMonoidHom.pi_apply,
    SelmerStructure.mem_selmerGroup_iff, selmerStructure_localization,
    selmerStructure_localCondition] at hc ⊢
  refine ⟨fun h i ↦ ?_, fun h v ↦ h (.inl v)⟩
  by_cases hi : i ∈ Sum.inl '' (S : Set (HeightOneSpectrum (𝓞 K)))
  · obtain ⟨v, hv, rfl⟩ := hi
    exact h ⟨v, hv⟩
  · exact hc i hi

/-- The order of the localisation of `Sel_φ̂` at the places of `S` is `[Sel_φ̂ : Sel_φ̂,S]`. -/
private theorem natCard_map_locDualRes :
    Nat.card ((φ.dual.selmerGroup τ).map (locDualRes φ τ S)) =
      ((φ.dual.selmerStructure τ).strictAt (Sum.inl '' S)).selmerGroup.relIndex
        (φ.dual.selmerGroup τ) := by
  rw [← AddSubgroup.relIndex_ker, ← AddSubgroup.inf_relIndex_right,
    ← AddSubgroup.inf_relIndex_right ((φ.dual.selmerStructure τ).strictAt _).selmerGroup]
  congr 1
  ext d
  rw [selmerGroup_def, AddSubgroup.mem_inf, AddSubgroup.mem_inf,
    SelmerStructure.mem_selmerGroup_strictAt_iff, AddMonoidHom.mem_ker]
  have key : locDualRes φ τ S d = 0 ↔ ∀ i ∈ Sum.inl '' (S : Set (HeightOneSpectrum (𝓞 K))),
      (φ.dual.selmerStructure τ).localization i d = 0 := by
    rw [funext_iff]
    refine ⟨?_, fun h v ↦ ?_⟩
    · rintro h _ ⟨v, hv, rfl⟩
      rw [selmerStructure_localization]
      exact (φ.dualKerRes_eq_zero_iff _).mp (h ⟨v, hv⟩)
    · have hv := h (.inl v) ⟨v, v.property, rfl⟩
      rw [selmerStructure_localization] at hv
      exact (φ.dualKerRes_eq_zero_iff _).mpr hv
  rw [key]
  exact ⟨fun ⟨h, hd⟩ ↦ ⟨⟨hd, h⟩, hd⟩, fun ⟨⟨hd, h⟩, _⟩ ↦ ⟨h, hd⟩⟩

private theorem natCard_pi :
    Nat.card (∀ v : S, H1 (AbsoluteGaloisGroup ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K))
      (ofIsogeny (φ.baseChange ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K))).KerCoeff) =
      Nat.card (localConditions φ S) *
        ∏ v ∈ S, (φ.baseChange (v.adicCompletion K)).localKummerCondition.index := by
  rw [Nat.card_pi, localConditions, AddSubgroup.card_pi,
    ← Finset.prod_coe_sort S fun v ↦
      (φ.baseChange (v.adicCompletion K)).localKummerCondition.index, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun v _ ↦ (AddSubgroup.card_mul_index _).symm

/-- **The orthogonality bound for the Selmer groups of an isogeny and its dual.** Let `φ : E₁ → E₂`
be an isogeny over a number field `K` and `S` a finite set of finite places of `K`. Then

`[Sel_φ^S : Sel_φ] · [Sel_φ̂ : Sel_φ̂,S] ≤ ∏_{v ∈ S} [H¹(K_v, E₁[φ]) : H¹_φ(K_v)]`,

where `Sel_φ^S` is the `φ`-Selmer group relaxed at `S`, `Sel_φ̂,S` is the `φ̂`-Selmer group strict
at `S`, and `H¹_φ(K_v)`, the local condition of `φ` at `v`, is the kernel of
`H¹(K_v, E₁[φ]) → H¹(K_v, E₁)`. Poitou–Tate duality would give equality. -/
theorem relIndex_selmerGroup_relaxedAt_mul_relIndex_strictAt_dual_le :
    (φ.selmerGroup τ).relIndex ((φ.selmerStructure τ).relaxedAt (Sum.inl '' S)).selmerGroup *
        ((φ.dual.selmerStructure τ).strictAt (Sum.inl '' S)).selmerGroup.relIndex
          (φ.dual.selmerGroup τ) ≤
      ∏ v ∈ S, (φ.baseChange (v.adicCompletion K)).localKummerCondition.index := by
  have h := natCard_sup_mul_natCard_map_le φ τ S
  rw [natCard_sup, natCard_map_locDualRes, natCard_pi] at h
  refine Nat.le_of_mul_le_mul_left (c := Nat.card (localConditions φ S)) ?_
    (Nat.card_pos (α := localConditions φ S))
  convert h using 1
  ring

end TauCeti.Isogeny
