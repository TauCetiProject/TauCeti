/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.Kummer.Norm
import TauCeti.NumberTheory.NumberField.Kummer.SUnitRadical

/-!
# Auxiliary Kummer norms for prime-degree extensions

Let `L/K` be a Galois extension of number fields of prime degree `p`, with the `p`-th roots
of unity in `K`. This file chooses the finite sets `S` and `T` used in the Kummer proof of
the second fundamental inequality, without requiring an embedding of `L` into an `S`-unit
Kummer field as input.

The set `S` can contain any prescribed finite set. It contains the places above `p` and
generates the class group, and is large enough that `L` embeds into `M = K(U_S^{1/p})`.
The auxiliary set `T` is disjoint from `S`, the `S`-units surject onto the local unit
power classes at `T`, and the auxiliary Kummer idele-class subgroup is contained in the
norm group of the original extension `L/K`. The cardinality identity
`#T + 1 = #S + #S_∞(K)` is the numerical input for the subsequent index computation.

The construction uses the radical description of cyclic extensions unramified outside `S`,
the auxiliary-place theorem inside `M`, and invariance of idele-class norm groups under
isomorphisms of extensions. In particular, the conclusion concerns `N_{L/K}(C_L)`, not just
the norm group of a chosen isomorphic subfield of `M`.

## Main result

* `TauCeti.ClassFieldTheory.exists_auxiliaryKummerNorms_of_finrank_prime`: choose `S` and `T`
  with the class-group, local-power, cardinality and norm-inclusion properties.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, §6, especially Lemma 6.9 and the
  proof of the second fundamental inequality.
-/

public noncomputable section

open IsDedekindDomain NumberField IntermediateField
open TauCeti.GlobalNumberFields

namespace TauCeti.ClassFieldTheory

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

/-- **Auxiliary Kummer norms for a prime-degree extension.** Suppose that `L/K` has prime
degree `p` and `K` contains the `p`-th roots of unity. Given any finite set `S₀` of finite
places of `K`, there are finite sets `S ⊇ S₀` and `T` such that `S` generates the class group
and contains the places above `p`, `S` and `T` are disjoint, `#T + 1 = #S + #S_∞(K)`, the
`S`-units surject onto the local unit `p`-th power classes at `T`, and the auxiliary Kummer
idele-class subgroup `E_{S,T}` is contained in `N_{L/K}(C_L)`. -/
theorem exists_auxiliaryKummerNorms_of_finrank_prime {p : ℕ} (hp : p.Prime)
    [HasEnoughRootsOfUnity K p] (hL : Module.finrank K L = p)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      S₀ ⊆ S ∧
      Subgroup.closure (HeightOneSpectrum.classGroupMk ''
        (S : Set (HeightOneSpectrum (𝓞 K)))) = ⊤ ∧
      (∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v ∈ S) ∧
      ∃ T : Finset (HeightOneSpectrum (𝓞 K)),
        ∃ hST : Disjoint (S : Set (HeightOneSpectrum (𝓞 K))) (T : Set _),
          T.card + 1 = Fintype.card (InfinitePlace K) + S.card ∧
          Function.Surjective (Set.unitLocalPowerClassMap
            (S : Set (HeightOneSpectrum (𝓞 K))) (T : Set _) hST p) ∧
          auxiliaryKummerIdeleClassSubgroup (K := K) S T p ≤
            (ideleClassNormMap K L : IdeleClassGroup (𝓞 L) L →*
              IdeleClassGroup (𝓞 K) K).range := by
  classical
  let _ : NeZero p := ⟨hp.ne_zero⟩
  -- Work in the separable closure, but retain the isomorphism back to the caller's extension.
  let ι : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let F := ι.fieldRange
  have : FiniteDimensional K F := ι.equivFieldRange.toLinearEquiv.finiteDimensional
  let _ : NumberField F := .of_module_finite K F
  have : IsGalois K F := IsGalois.of_algEquiv ι.equivFieldRange
  have hF : Module.finrank K F = p := ι.equivFieldRange.toLinearEquiv.finrank_eq.symm.trans hL
  have : Fact (Nat.card Gal(F/K)).Prime := ⟨by rw [IsGalois.card_aut_eq_finrank, hF]; exact hp⟩
  have : IsCyclic Gal(F/K) := isCyclic_of_prime_card (p := Nat.card Gal(F/K)) rfl
  -- Enlarge the prescribed set by class generators, ramified places and places above `p`.
  obtain ⟨S, hS₀S, hcl, hpS⟩ := ClassGroup.exists_finset_superset_closure_classGroupMk_image_eq_top
    (S₀ ∪ TauCeti.NumberField.ramifiedSupport K F) (a := (p : 𝓞 K))
    (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hur (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ (S : Set _)) :
      ∃ w : HeightOneSpectrum (𝓞 F), w.asIdeal.LiesOver v.asIdeal ∧
        Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal := by
    obtain ⟨w, hw⟩ := HeightOneSpectrum.under_surjective (𝓞 K) (𝓞 F) v
    have : w.asIdeal.LiesOver v.asIdeal := hw ▸ inferInstance
    refine ⟨w, inferInstance, TauCeti.NumberField.isUnramifiedAway_ramifiedSupport v ?_
      w.asIdeal⟩
    exact fun hram ↦ hv (hS₀S (Finset.mem_union_right _ hram))
  let M := kummerField (SeparableClosure K) p ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)
  have hFM : F ≤ M := TauCeti.NumberField.le_kummerField_sUnits_of_isCyclic hcl hF.dvd hur
  let F' := IntermediateField.restrict hFM
  let _ : Algebra F' M := F'.toAlgebra
  let _ : IsScalarTower K F' M := F'.isScalarTower_mid'
  let e : L ≃ₐ[K] F' := ι.equivFieldRange.trans (IntermediateField.restrictAlgEquiv hFM)
  have hF' : Module.finrank K F' = p := e.toLinearEquiv.finrank_eq.symm.trans hL
  have : FiniteDimensional K F' := e.toLinearEquiv.finiteDimensional
  let _ : NumberField F' := .of_module_finite K F'
  have hroots (a : Kˣ) (_ha : a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) :
      ∃ x : SeparableClosure K, x ^ p = algebraMap K (SeparableClosure K) (a : K) :=
    IsSepClosed.exists_pow_nat_eq _ p
  have : (powMonoidHom p : Kˣ →* Kˣ).range.IsFiniteRelIndex
      ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) :=
    ⟨by rw [relIndex_range_powMonoidHom_sUnits_numberField]; exact pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot K p
  obtain ⟨T, hST, hcard, hsurj, hnorm⟩ :=
    exists_auxiliaryKummerIdeleClassSubgroup_le_range_ideleClassNormMap hp S hpS
      hζ.toInteger_isPrimitiveRoot hroots F'
  have hdegree : Module.finrank K M = p ^ (Fintype.card (InfinitePlace K) + S.card) := by
    rw [finrank_kummerField hroots, relIndex_range_powMonoidHom_sUnits_numberField,
      Nat.card_coe_set_eq, Set.ncard_coe_finset]
  -- Bypass intermediate-field module inference when applying the tower formula.
  have : Module.Free F' M := Module.Free.of_divisionRing F' M
  have hcount : T.card + 1 = Fintype.card (InfinitePlace K) + S.card := by
    apply Nat.pow_right_injective hp.two_le
    calc
      p ^ (T.card + 1) = p ^ T.card * p := pow_succ _ _
      _ = Module.finrank F' M * Module.finrank K F' := congrArg₂ (· * ·) hcard hF'.symm
      _ = Module.finrank K M := (mul_comm _ _).trans (Module.finrank_mul_finrank K F' M)
      _ = p ^ (Fintype.card (InfinitePlace K) + S.card) := hdegree
  refine ⟨S, Finset.union_subset_left hS₀S, hcl, hpS, T, hST, hcount, hsurj, ?_⟩
  exact (range_ideleClassNormMap_eq_of_algEquiv e).symm ▸ hnorm

end TauCeti.ClassFieldTheory
