/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.ExponentNorms
public import TauCeti.NumberTheory.ClassFieldTheory.Global.Kummer.Ideles
public import TauCeti.NumberTheory.NumberField.Discriminant.RamifiedSupport.Basic

public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Surjective
public import TauCeti.NumberTheory.NumberField.Kummer.LocalDegree
import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.Norm.Units

/-!
# Kummer idele subgroups contained in norm groups

Let `L/K` be a finite Galois extension of number fields whose Galois group has exponent dividing
`n`. If a finite set `S` contains every prime ramified in `L`, then the Kummer idele subgroup
`E_S` of ideles that are local `n`-th powers at `S` and at infinity, and units outside `S`, is
contained in the idele norm group of `L/K`. Consequently its image in the idele class group is
contained in the idele-class norm group.

The proof is placewise. At the places of `S` and at infinity, exponent divisibility makes every
`n`-th power a local norm. Outside `S`, the extension is unramified and local units are norms.
The resulting inclusion is the norm half of the Kummer computation of the second fundamental
inequality. It converts the index of the idele-class norm group into a divisor of the index of the
Kummer idele-class subgroup.

If the extension is the Kummer field of radicands that are local powers at `S` and at infinity,
and units outside `S`, then every idele class is a norm, provided `S` contains the places above
`n` and generates the class group. The places of `S` and infinity split completely, and the
extension is unramified elsewhere. An auxiliary set `T` is also allowed when the `S`-units
control the local power classes at `T`, as in Milne's Proposition 6.10.

## Main statements

* `TauCeti.ClassFieldTheory.kummerIdeleSubgroup_le_range_ideleNormMap`: the Kummer idele subgroup
  is contained in the idele norm group.
* `TauCeti.ClassFieldTheory.kummerIdeleClassSubgroup_le_range_ideleClassNormMap`: the corresponding
  inclusion after passage to idele classes.
* `TauCeti.ClassFieldTheory.index_range_ideleClassNormMap_dvd_index_kummerIdeleClassSubgroup`:
  the resulting divisibility of indices.

* `TauCeti.ClassFieldTheory.ideleClassNormMap_kummerField_surjective`: surjectivity for radicands
  represented by the Kummer idele subgroup.
* `TauCeti.ClassFieldTheory.ideleClassNormMap_kummerField_surjective_of_forall_exists_mem_unit`:
  surjectivity with an auxiliary set of places.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, §§5--6, Proposition 6.10 and §9.
* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter VII, §6.
-/

public section

noncomputable section

open IsDedekindDomain NumberField

namespace TauCeti.ClassFieldTheory

variable (K : Type) [Field K] [NumberField K]
variable (L : Type*) [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

/-- **The Kummer idele subgroup consists of norms.** If the exponent of `Gal(L/K)` divides `n`
and `S` contains every finite place ramified in `L`, then every idele in the Kummer subgroup
`E_S` is the norm of an idele of `L`. -/
theorem kummerIdeleSubgroup_le_range_ideleNormMap {n : ℕ}
    (hn : Monoid.exponent Gal(L/K) ∣ n) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hram : TauCeti.NumberField.ramifiedSupport K L ⊆ S) :
    kummerIdeleSubgroup S n ≤
      (GlobalNumberFields.ideleNormMap K L).toMonoidHom.range := by
  intro x hx
  rw [mem_kummerIdeleSubgroup_iff] at hx
  refine mem_range_ideleNormMap_of_exponent_dvd K L hn (S := (S : Set _)) (T := ∅)
    (by simp) ?_ ?_ ?_ ?_
  · intro v hvS _
    obtain ⟨w, rfl⟩ := HeightOneSpectrum.under_surjective (𝓞 K) (𝓞 L) v
    exact ⟨⟨w, inferInstance⟩, TauCeti.NumberField.isUnramifiedAway_ramifiedSupport _
      (fun hv ↦ hvS (hram hv)) w.asIdeal⟩
  · intro v hvS
    rw [powerSubgroup_eq_range_powMonoidHom]
    exact hx.1 v hvS
  · intro v hvS _
    exact hx.2.2 v hvS
  · intro v
    rw [powerSubgroup_eq_range_powMonoidHom]
    exact hx.2.1 v

/-- **The Kummer idele-class subgroup consists of norms.** Under the same hypotheses as
`kummerIdeleSubgroup_le_range_ideleNormMap`, every class represented by a Kummer idele is in
`N_{L/K}(C_L)`. -/
theorem kummerIdeleClassSubgroup_le_range_ideleClassNormMap {n : ℕ}
    (hn : Monoid.exponent Gal(L/K) ∣ n) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hram : TauCeti.NumberField.ramifiedSupport K L ⊆ S) :
    kummerIdeleClassSubgroup S n ≤
      (GlobalNumberFields.ideleClassNormMap K L :
        IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K).range := by
  intro c hc
  obtain ⟨x, hx, rfl⟩ := (mem_kummerIdeleClassSubgroup_iff S n c).mp hc
  obtain ⟨y, hy⟩ := kummerIdeleSubgroup_le_range_ideleNormMap K L hn S hram hx
  refine ⟨(y : IdeleClassGroup (𝓞 L) L), ?_⟩
  exact (GlobalNumberFields.ideleClassNormMap_mk y).trans
    (congrArg (fun z : IdeleGroup (𝓞 K) K ↦ (z : IdeleClassGroup (𝓞 K) K)) hy)

/-- **The idele-class norm index divides the Kummer subgroup index.** If `S` contains the
ramified places and `n` is divisible by the exponent of `Gal(L/K)`, then
`[C_K : N_{L/K}(C_L)]` divides `[C_K : E_S]`. -/
theorem index_range_ideleClassNormMap_dvd_index_kummerIdeleClassSubgroup {n : ℕ}
    (hn : Monoid.exponent Gal(L/K) ∣ n) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hram : TauCeti.NumberField.ramifiedSupport K L ⊆ S) :
    (GlobalNumberFields.ideleClassNormMap K L :
        IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K).range.index ∣
      (kummerIdeleClassSubgroup S n).index :=
  Subgroup.index_dvd_of_le
    (kummerIdeleClassSubgroup_le_range_ideleClassNormMap K L hn S hram)

end TauCeti.ClassFieldTheory

namespace TauCeti.ClassFieldTheory

open TauCeti.NumberField TauCeti.GlobalNumberFields

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
