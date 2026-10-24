/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.Kummer.AuxiliaryIdeles
public import TauCeti.NumberTheory.ClassFieldTheory.Global.Kummer.AuxiliaryPlaces
public import TauCeti.NumberTheory.NumberField.Discriminant.RamifiedSupport.Basic

public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Surjective
public import TauCeti.NumberTheory.NumberField.Kummer.LocalDegree
import TauCeti.NumberTheory.NumberField.Discriminant.RamifiedSupport.Tower
import TauCeti.NumberTheory.NumberField.Kummer.Unramified
import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.Norm.Units
import TauCeti.RingTheory.RootsOfUnity.Basic

/-!
# Kummer idele subgroups contained in norm groups

Let `L/K` be a finite Galois extension of number fields whose Galois group has exponent dividing
`n`. If a finite set `S` contains every prime ramified in `L`, then the Kummer idele subgroup
`E_S` of ideles that are local `n`-th powers at `S` and at infinity, and units outside `S`, is
contained in the idele norm group of `L/K`. Consequently its image in the idele class group is
contained in the idele-class norm group. The same holds for the auxiliary subgroup `E_{S,T}`,
whose components at a further finite set `T` are local units, when every place of `T` outside
`S` has a place of `L` above it of local degree one.

The proof is placewise. At the places of `S` and at infinity, exponent divisibility makes every
`n`-th power a local norm. At the places of `T`, local degree one makes every local element a
norm. Elsewhere, the extension is unramified and local units are norms.
The resulting inclusion is the norm half of the Kummer computation of the second fundamental
inequality. It converts the index of the idele-class norm group into a divisor of the index of the
Kummer idele-class subgroup.

For an intermediate field `L` of the Kummer field `M = K(U_S^{1/p})`, the Frobenius choice of an
auxiliary set `T` gives places of local degree one in `L`, so the auxiliary idele-class subgroup
`E_{S,T}` with `p ^ #T = [M : L]` is contained in `N_{L/K}(C_L)`.

If the extension is the Kummer field of radicands that are local powers at `S` and at infinity,
and units outside `S`, then every idele class is a norm, provided `S` contains the places above
`n` and generates the class group. The places of `S` and infinity split completely, and the
extension is unramified elsewhere. An auxiliary set `T` is also allowed when the `S`-units
control the local power classes at `T`, as in Milne's Proposition 6.10.

## Main statements

* `auxiliaryKummerIdeleSubgroup_le_range_ideleNormMap_of_ramifiedSupport`:
  the auxiliary Kummer idele subgroup is contained in the idele norm group.
* `auxiliaryKummerIdeleClassSubgroup_le_range_ideleClassNormMap_of_ramifiedSupport`:
  the corresponding inclusion after passage to idele classes.
* The index divisibility theorem with suffix `_of_ramifiedSupport`:
  the resulting divisibility of indices.
* `TauCeti.ClassFieldTheory.exists_auxiliaryKummerIdeleClassSubgroup_le_range_ideleClassNormMap`:
  the auxiliary set `T` for an intermediate Kummer field, its counting and local-power-class
  properties, and the inclusion of its idele-class subgroup in the norm subgroup from `L`.

* `TauCeti.ClassFieldTheory.ideleClassNormMap_kummerField_surjective`: surjectivity for radicands
  represented by the Kummer idele subgroup.
* `TauCeti.ClassFieldTheory.ideleClassNormMap_kummerField_surjective_of_forall_exists_mem_unit`:
  surjectivity with an auxiliary set of places.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, §§5--6, Lemmas 6.4, 6.6 and 6.9,
  Proposition 6.10 and §9.
* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter VII, §6.
-/

public section

noncomputable section

open IsDedekindDomain NumberField
open scoped AdicCompletionExtension

namespace TauCeti.ClassFieldTheory

variable (K : Type) [Field K] [NumberField K]
variable (L : Type*) [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

/-- **The Kummer idele subgroup consists of norms.** If the exponent of `Gal(L/K)` divides `n`
and `S` contains every finite place ramified in `L`, then every idele in the Kummer subgroup
`E_{S,T}` is the norm of an idele of `L`, provided every place of `T` outside `S` has a place of
`L` above it of local degree one. -/
theorem auxiliaryKummerIdeleSubgroup_le_range_ideleNormMap_of_ramifiedSupport {n : ℕ}
    (hn : Monoid.exponent Gal(L/K) ∣ n) (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ v ∈ T, v ∉ S →
      ∃ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
      Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = 1)
    (hram : TauCeti.NumberField.ramifiedSupport K L ⊆ S) :
    auxiliaryKummerIdeleSubgroup S T n ≤
      (GlobalNumberFields.ideleNormMap K L).toMonoidHom.range := by
  apply auxiliaryKummerIdeleSubgroup_le_range_ideleNormMap K L hn S T hT
  intro v hvS _
  obtain ⟨w, rfl⟩ := HeightOneSpectrum.under_surjective (𝓞 K) (𝓞 L) v
  exact ⟨⟨w, inferInstance⟩, TauCeti.NumberField.isUnramifiedAway_ramifiedSupport _
    (fun hv ↦ hvS (hram hv)) w.asIdeal⟩

/-- **The Kummer idele-class subgroup consists of norms.** Under the same hypotheses as
`auxiliaryKummerIdeleSubgroup_le_range_ideleNormMap_of_ramifiedSupport`, every class represented
by a Kummer idele is in `N_{L/K}(C_L)`. -/
theorem auxiliaryKummerIdeleClassSubgroup_le_range_ideleClassNormMap_of_ramifiedSupport {n : ℕ}
    (hn : Monoid.exponent Gal(L/K) ∣ n) (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ v ∈ T, v ∉ S →
      ∃ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
      Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = 1)
    (hram : TauCeti.NumberField.ramifiedSupport K L ⊆ S) :
    auxiliaryKummerIdeleClassSubgroup S T n ≤
      (GlobalNumberFields.ideleClassNormMap K L :
        IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K).range := by
  apply auxiliaryKummerIdeleClassSubgroup_le_range_ideleClassNormMap K L hn S T hT
  intro v hvS _
  obtain ⟨w, rfl⟩ := HeightOneSpectrum.under_surjective (𝓞 K) (𝓞 L) v
  exact ⟨⟨w, inferInstance⟩, TauCeti.NumberField.isUnramifiedAway_ramifiedSupport _
    (fun hv ↦ hvS (hram hv)) w.asIdeal⟩

/-- **The idele-class norm index divides the Kummer subgroup index.** If `S` contains the
ramified places and `n` is divisible by the exponent of `Gal(L/K)`, then
`[C_K : N_{L/K}(C_L)]` divides `[C_K : E_{S,T}]` whenever every place of `T` outside `S` has a
place of `L` above it of local degree one. -/
theorem index_range_ideleClassNormMap_dvd_index_auxiliaryKummerIdeleClassSubgroup_of_ramifiedSupport
    {n : ℕ}
    (hn : Monoid.exponent Gal(L/K) ∣ n) (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ v ∈ T, v ∉ S →
      ∃ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
      Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = 1)
    (hram : TauCeti.NumberField.ramifiedSupport K L ⊆ S) :
    (GlobalNumberFields.ideleClassNormMap K L :
        IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K).range.index ∣
      (auxiliaryKummerIdeleClassSubgroup S T n).index :=
  Subgroup.index_dvd_of_le
    (auxiliaryKummerIdeleClassSubgroup_le_range_ideleClassNormMap_of_ramifiedSupport
      K L hn S T hT hram)

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
    (hΔ : ∀ a ∈ Δ,
      IdeleGroup.unitEmbedding (𝓞 K) K a ∈ auxiliaryKummerIdeleSubgroup S ∅ n) :
    Function.Surjective (ideleClassNormMap K (kummerField E n Δ)) := by
  have hmem (a) (ha : a ∈ Δ) :=
    (mem_auxiliaryKummerIdeleSubgroup_iff S ∅ n _).mp (hΔ a ha)
  refine ideleClassNormMap_kummerField_surjective_of_forall_exists_mem_unit S ∅
    (Finset.disjoint_empty_right S) hcl hnS (fun a ha ↦ ?_) (fun v hv a ha ↦ ?_)
    (fun w a ha ↦ ?_) dvd_rfl fun _ _ ↦ ⟨1, one_mem _, fun v ↦ (Finset.notMem_empty _ v.2).elim⟩
  · rw [Finset.coe_empty, Set.union_empty,
      ← IdeleGroup.forall_valued_ideleFiniteCoord_unitEmbedding_eq_one_iff (R := 𝓞 K)]
    exact fun v hvS ↦ (hmem a ha).2.2 v hvS (by simp)
  · obtain ⟨c, hc⟩ := (hmem a ha).1 v hv
    exact ⟨c, by simpa using congrArg Units.val hc⟩
  · obtain ⟨c, hc⟩ := (hmem a ha).2.1 w
    exact ⟨c, by simpa using congrArg Units.val hc⟩

end TauCeti.ClassFieldTheory

namespace TauCeti.ClassFieldTheory

variable {K E : Type} [Field K] [NumberField K] [Field E] [Algebra K E]

/-- **The auxiliary Kummer idele classes are norms from an intermediate Kummer field.**
Let `M = K(U_S^{1/p})`, where `S` contains the places above the prime `p`, and let `L/K` be an
intermediate field of `M/K`. There is a finite set `T`, disjoint from `S`, such that
`p ^ #T = [M : L]`, the `S`-units surject onto the local unit `p`-th power classes at `T`, and
the image in `C_K` of the auxiliary Kummer subgroup `E_{S,T}` is contained in
`N_{L/K}(C_L)`. -/
theorem exists_auxiliaryKummerIdeleClassSubgroup_le_range_ideleClassNormMap
    {p : ℕ} (hp : p.Prime) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hpS : ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p)
    (hroots : ∀ a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K,
      ∃ x : E, x ^ p = algebraMap K E (a : K))
    (L : IntermediateField K
      (kummerField E p ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))) [NumberField L] :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)),
      ∃ hST : Disjoint (S : Set (HeightOneSpectrum (𝓞 K))) (T : Set _),
        p ^ T.card = Module.finrank L
            (kummerField E p ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) ∧
          Function.Surjective
            (Set.unitLocalPowerClassMap (S : Set (HeightOneSpectrum (𝓞 K))) (T : Set _) hST p) ∧
          auxiliaryKummerIdeleClassSubgroup (K := K) S T p ≤
            (GlobalNumberFields.ideleClassNormMap K L :
              IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K).range := by
  let M := kummerField E p ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)
  let _ : NeZero p := ⟨hp.ne_zero⟩
  have : HasEnoughRootsOfUnity K p :=
    hasEnoughRootsOfUnity_of_isPrimitiveRoot
      (hζ.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 K) K))
  obtain ⟨T, hST, hcard, hsurj, hsplit⟩ :=
    exists_auxiliaryPlaces_unitLocalPowerClassMap_surjective hp S hpS hζ hroots L
  have hram : TauCeti.NumberField.ramifiedSupport K L ⊆ S := fun _ hv ↦
    TauCeti.NumberField.ramifiedSupport_kummerField_sUnits_subset S hpS
      (NumberField.ramifiedSupport_mono K (L := L) (M := M) hv)
  have hMexp : Monoid.exponent (M ≃ₐ[K] M) ∣ p := exponent_algEquiv_kummerField_dvd
  exact ⟨T, hST, hcard, hsurj,
    auxiliaryKummerIdeleClassSubgroup_le_range_ideleClassNormMap_of_ramifiedSupport K L
      ((MonoidHom.exponent_dvd (AlgEquiv.restrictNormalHom_surjective M)).trans hMexp) S T
      (fun v hv _ ↦ hsplit v hv) hram⟩

end TauCeti.ClassFieldTheory
