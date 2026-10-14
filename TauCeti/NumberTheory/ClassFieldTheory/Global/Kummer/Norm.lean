/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.Kummer.Ideles
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Surjective
public import TauCeti.NumberTheory.NumberField.Kummer.LocalDegree
import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.Norm.Units

/-!
# Idele classes are norms from the Kummer field of local powers

Let `K` be a number field containing the `n`-th roots of unity and let `S` be a finite set of
finite places of `K` containing the places above `n`, whose classes generate the ideal class
group. Let `Δ` be a subgroup of `S`-units that are `n`-th powers in `K_v` at every place `v ∈ S`
and at every infinite place: in idelic terms, the principal ideles of `Δ` lie in the Kummer idele
subgroup `kummerIdeleSubgroup S n`. Then every idele class of `K` is a norm from the Kummer field
`M = K(Δ^{1/n})` (`TauCeti.ClassFieldTheory.ideleClassNormMap_kummerField_surjective`).

Indeed, the places of `S` and the infinite places split completely in `M`
(`TauCeti.NumberField.finrank_adicCompletion_kummerField_eq_one` and
`TauCeti.NumberField.finrank_completion_kummerField_eq_one`), so every element of `K_v` is a local
norm there, and `M` is unramified outside `S`
(`TauCeti.NumberField.isUnramifiedIn_kummerField_of_valuation_eq_one`). These are the local
hypotheses of Milne's Proposition 6.10,
`TauCeti.GlobalNumberFields.ideleClassNormMap_surjective_of_forall_exists_mem_unit`. More generally
the radicands may be units only outside `S ∪ T` for a second finite set `T`, provided the
`S`-units surject onto `∏_{v ∈ T} U_v / U_v ^ m` for a multiple `m` of `[M : K]`
(`TauCeti.ClassFieldTheory.ideleClassNormMap_kummerField_surjective_of_forall_exists_mem_unit`).

Combined with the first fundamental inequality, which forbids a nontrivial cyclic extension from
which every idele class is a norm, this shows that such a `Δ` consists of `n`-th powers: an
`S`-unit that is an `n`-th power at the places of `S` and at the infinite places is an `n`-th
power. That is the intersection `U_S ∩ E_S = U_S ^ n` of the `S`-units with the Kummer idele
subgroup, which turns the index of the idelic subgroup into the index of its image in the idele
class group. With `T`, the same argument applies to the subgroup `E_{S,T}` of the Kummer proof of
the second fundamental inequality.

## Main results

* `TauCeti.ClassFieldTheory.ideleClassNormMap_kummerField_surjective_of_forall_exists_mem_unit`:
  the norm map `C_M → C_K` is onto when the radicands are `S ∪ T`-units, local `n`-th powers at
  `S` and at the infinite places, and the `S`-units control the local power classes at `T`.
* `TauCeti.ClassFieldTheory.ideleClassNormMap_kummerField_surjective`: the case `T = ∅`, stated
  through the Kummer idele subgroup.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, Proposition 6.10 and §9.
* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter VII, §6.
-/

public noncomputable section

open IsDedekindDomain NumberField TauCeti.NumberField TauCeti.GlobalNumberFields

namespace TauCeti.ClassFieldTheory

variable {K E : Type*} [Field K] [NumberField K] [Field E] [Algebra K E]
  {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n] {Δ : Subgroup Kˣ}
  [(powMonoidHom n : Kˣ →* Kˣ).range.IsFiniteRelIndex Δ]

/-- **Idele classes are norms from a Kummer field of local powers, with an auxiliary set `T`.**
Let `S` and `T` be disjoint finite sets of finite places of `K`, with `S` containing the places
above `n` and generating the ideal class group. Let `Δ` consist of `S ∪ T`-units that are `n`-th
powers in `K_v` at every `v ∈ S` and at every infinite place, and let `m` be a multiple of the
degree of `M = K(Δ^{1/n})` such that the `S`-units surject onto `∏_{v ∈ T} U_v / U_v ^ m`. Then
the norm map `C_M → C_K` of idele classes is surjective. -/
theorem ideleClassNormMap_kummerField_surjective_of_forall_exists_mem_unit
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hST : Disjoint S T)
    (hcl : Subgroup.closure
      (HeightOneSpectrum.classGroupMk '' (S : Set (HeightOneSpectrum (𝓞 K)))) = ⊤)
    (hnS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hΔ : Δ ≤ ((S ∪ T : Set (HeightOneSpectrum (𝓞 K)))).unit K)
    (hΔS : ∀ v ∈ S, ∀ a ∈ Δ, ∃ c : v.adicCompletion K, c ^ n = algebraMap K _ a)
    (hΔinf : ∀ w : InfinitePlace K, ∀ a ∈ Δ, ∃ c : w.Completion, c ^ n = algebraMap K _ a)
    {m : ℕ} (hm : Module.finrank K (kummerField E n Δ) ∣ m)
    (hT : ∀ y : (v : T) → (v.1.adicCompletion K)ˣ,
      (∀ v, Valued.v (y v : v.1.adicCompletion K) = 1) →
      ∃ u ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K, ∀ v : T,
        (Units.map (algebraMap K (v.1.adicCompletion K)).toMonoidHom u)⁻¹ * y v ∈
          (powMonoidHom m).range) :
    Function.Surjective (ideleClassNormMap K (kummerField E n Δ)) := by
  classical
  -- A finite place of `M` above each finite place of `K`.
  have hw (v : HeightOneSpectrum (𝓞 K)) :
      Nonempty {w : HeightOneSpectrum (𝓞 (kummerField E n Δ)) // w.asIdeal.LiesOver v.asIdeal} := by
    obtain ⟨P, hP, hPv⟩ :=
      Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 (kummerField E n Δ)) v.asIdeal
    exact ⟨⟨⟨P, hP.isPrime, Ideal.ne_bot_of_mem_primesOver v.ne_bot ⟨hP.isPrime, hPv⟩⟩, hPv⟩⟩
  refine ideleClassNormMap_surjective_of_forall_exists_mem_unit S T hST hm hcl
    (fun v hv ↦ eq_top_iff.mpr fun a _ ↦ ?_) (fun v ↦ eq_top_iff.mpr fun a _ ↦ ?_)
    (fun v hvS hvT ↦ ?_) hT
  · -- At a place of `S` the Kummer field splits completely.
    obtain ⟨w, _⟩ := hw v
    exact mem_range_normUnits_adicCompletion_of_finrank_eq_one K _ v
      ⟨⟨w, ‹_›⟩, finrank_adicCompletion_kummerField_eq_one (hΔS v hv) w⟩ a
  · -- So it does at an infinite place.
    obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (k := K) (K := kummerField E n Δ) v
    have : w.LiesOver v := hw ▸ inferInstance
    exact mem_range_normUnits_completion_of_finrank_eq_one K _ v
      ⟨⟨w, this⟩, finrank_completion_kummerField_eq_one (hΔinf v) w⟩ a
  · -- Outside `S ∪ T` the radicands and `n` are units, so the Kummer field is unramified.
    obtain ⟨w, _⟩ := hw v
    have hur := isUnramifiedIn_kummerField_of_valuation_eq_one (E := E) (Δ := Δ)
      (fun h ↦ hvS (hnS v h)) fun a ha ↦ (Set.mem_unit_iff _ K).mp (hΔ ha) v (by simp [hvS, hvT])
    exact ⟨⟨w, ‹_›⟩, hur w.asIdeal w.isPrime ‹_›⟩

/-- **Idele classes are norms from the Kummer field of local powers.** Let `S` be a finite set of
finite places of `K` containing the places above `n` and generating the ideal class group. If the
principal idele of every element of `Δ` lies in the Kummer idele subgroup `E_S`, that is, every
element of `Δ` is an `S`-unit that is an `n`-th power at the places of `S` and at the infinite
places, then every idele class of `K` is a norm from `K(Δ^{1/n})`. -/
theorem ideleClassNormMap_kummerField_surjective (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hcl : Subgroup.closure
      (HeightOneSpectrum.classGroupMk '' (S : Set (HeightOneSpectrum (𝓞 K)))) = ⊤)
    (hnS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hΔ : ∀ a ∈ Δ, IdeleGroup.unitEmbedding (𝓞 K) K a ∈ kummerIdeleSubgroup S n) :
    Function.Surjective (ideleClassNormMap K (kummerField E n Δ)) := by
  have hmem (a) (ha : a ∈ Δ) := (mem_kummerIdeleSubgroup_iff S n _).mp (hΔ a ha)
  refine ideleClassNormMap_kummerField_surjective_of_forall_exists_mem_unit S ∅
    (Finset.disjoint_empty_right S) hcl hnS (fun a ha ↦ ?_) (fun v hv a ha ↦ ?_)
    (fun w a ha ↦ ?_) dvd_rfl fun _ _ ↦ ⟨1, one_mem _, fun v ↦ (Finset.notMem_empty _ v.2).elim⟩
  · rw [Finset.coe_empty, Set.union_empty,
      ← IdeleGroup.forall_valued_ideleFiniteCoord_unitEmbedding_eq_one_iff (R := 𝓞 K)]
    exact (hmem a ha).2.2
  · obtain ⟨c, hc⟩ := (hmem a ha).1 v hv
    exact ⟨c, by simpa using congrArg Units.val hc⟩
  · obtain ⟨c, hc⟩ := (hmem a ha).2.1 w
    exact ⟨c, by simpa using congrArg Units.val hc⟩

end TauCeti.ClassFieldTheory
