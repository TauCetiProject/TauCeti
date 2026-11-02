/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.Subdomain.Basic
public import TauCeti.RingTheory.AdicCompletion.AlgHom

/-!
# Adic completions along affinoid subdomains

If `φ : A → B` represents an affinoid subdomain `U` and all classical points of `V(I)`
lie in `U`, restriction induces an isomorphism between the `I`-adic completion of `A`
and the `IB`-adic completion of `B`. In particular the completions at corresponding
maximal ideals agree. These are ideal-adic completions, not Banach completions.

The isomorphism is the map induced by `φ`, and commutes with the projections to all
infinitesimal neighbourhoods. It follows by taking inverse limits of the existing
quotient isomorphisms. This is the formal-neighbourhood comparison used in the local
study of affinoid subdomains; no reducedness or chosen algebra norm is required.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §7.2.2.
-/

public section

namespace TauCeti.IsAffinoidSubdomainMap

open AdicCompletion

universe u

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    {A B : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    {φ : A →ₐ[K] B} {U : Set (MaximalSpectrum A)}
    (h : IsAffinoidSubdomainMap φ U) (hA : IsAffinoidAlgebra K A)

/-- Restriction to an affinoid subdomain preserves the completion along any ideal whose
classical zero locus is contained in the subdomain. The forward map is induced by `φ`. -/
noncomputable def completionAlgEquiv {I : Ideal A}
    (hI : ∀ x : MaximalSpectrum A, I ≤ x.asIdeal → x ∈ U) :
    AdicCompletion I A ≃ₐ[K] AdicCompletion (I.map φ) B := by
  let e (n : ℕ) : (A ⧸ I ^ n) ≃ₐ[K] B ⧸ (I.map φ) ^ n :=
    (h.quotientAlgEquiv hA fun x hx ↦ hI x (Ideal.IsPrime.le_of_pow_le hx)).trans
      (Ideal.quotientEquivAlgOfEq K (Ideal.map_pow φ I n))
  have he (n : ℕ) (a : A) :
      e n (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (φ a) := by simp [e]
  have heval (n : ℕ) (z : AdicCompletion I A) :
      evalₐ (I.map φ) n (mapₐ φ Ideal.le_comap_map z) = e n (evalₐ I n z) := by
    rw [evalₐ_mapₐ]
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (evalₐ I n z)
    rw [← ha, he]
    exact Ideal.quotientMap_mk
  -- The quotient comparisons commute with the transitions; so do their inverses.
  have htransition {m n : ℕ} (hle : m ≤ n) (z : A ⧸ I ^ n) :
      e m (Ideal.Quotient.factor (Ideal.pow_le_pow_right hle) z) =
        Ideal.Quotient.factor (Ideal.pow_le_pow_right hle) (e n z) := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    simp [he]
  let g (n : ℕ) : AdicCompletion (I.map φ) B →ₐ[K] A ⧸ I ^ n :=
    (e n).symm.toAlgHom.comp ((evalₐ (I.map φ) n).restrictScalars K)
  have hg {m n : ℕ} (hle : m ≤ n) :
      (Ideal.Quotient.factorₐ K (Ideal.pow_le_pow_right hle)).comp (g n) = g m := by
    ext z
    apply (e m).injective
    simp only [AlgHom.comp_apply, g, AlgHom.restrictScalars_apply, AlgEquiv.coe_toAlgHom,
      Ideal.Quotient.factorₐ_apply, htransition hle, AlgEquiv.apply_symm_apply]
    exact factor_evalₐ hle z
  -- Lift the compatible inverse maps, and check both composites on every projection.
  refine AlgEquiv.ofAlgHom (mapₐ φ Ideal.le_comap_map) (liftAlgHom I g hg) ?_ ?_
  · apply AlgHom.ext
    intro z
    apply ext_evalₐ
    intro n
    rw [AlgHom.comp_apply, AlgHom.id_apply, heval, evalₐ_liftAlgHom]
    exact (e n).apply_symm_apply _
  · apply AlgHom.ext
    intro z
    apply ext_evalₐ
    intro n
    rw [AlgHom.comp_apply, AlgHom.id_apply, evalₐ_liftAlgHom]
    dsimp only [g, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgHom.restrictScalars_apply]
    rw [heval]
    exact (e n).symm_apply_apply _

/-- The completion comparison is the canonical map of completions induced by restriction. -/
@[simp]
theorem toAlgHom_completionAlgEquiv {I : Ideal A}
    (hI : ∀ x : MaximalSpectrum A, I ≤ x.asIdeal → x ∈ U) :
    (h.completionAlgEquiv hA hI).toAlgHom = mapₐ φ Ideal.le_comap_map :=
  (rfl)

/-- The completion comparison extends the affinoid restriction map. -/
@[simp]
theorem completionAlgEquiv_of {I : Ideal A}
    (hI : ∀ x : MaximalSpectrum A, I ≤ x.asIdeal → x ∈ U) (a : A) :
    h.completionAlgEquiv hA hI (of I A a) = of (I.map φ) B (φ a) :=
  mapₐ_of φ Ideal.le_comap_map a

/-- On the image of `A`, the inverse completion comparison is the original completion map. -/
@[simp]
theorem completionAlgEquiv_symm_of {I : Ideal A}
    (hI : ∀ x : MaximalSpectrum A, I ≤ x.asIdeal → x ∈ U) (a : A) :
    (h.completionAlgEquiv hA hI).symm (of (I.map φ) B (φ a)) = of I A a := by
  rw [← h.completionAlgEquiv_of hA hI, AlgEquiv.symm_apply_apply]

/-- Modulo every power, the completion comparison is the quotient map induced by `φ`. -/
@[simp]
theorem evalₐ_completionAlgEquiv {I : Ideal A}
    (hI : ∀ x : MaximalSpectrum A, I ≤ x.asIdeal → x ∈ U)
    (n : ℕ) (z : AdicCompletion I A) :
    evalₐ (I.map φ) n (h.completionAlgEquiv hA hI z) =
      Ideal.quotientMap ((I.map φ) ^ n) φ.toRingHom
        ((Ideal.pow_right_mono Ideal.le_comap_map n).trans (Ideal.le_comap_pow _ n))
        (evalₐ I n z) :=
  evalₐ_mapₐ φ Ideal.le_comap_map n z

/-- Modulo every power, the inverse completion comparison is the inverse quotient comparison. -/
@[simp]
theorem evalₐ_completionAlgEquiv_symm {I : Ideal A}
    (hI : ∀ x : MaximalSpectrum A, I ≤ x.asIdeal → x ∈ U)
    (n : ℕ) (w : AdicCompletion (I.map φ) B) :
    evalₐ I n ((h.completionAlgEquiv hA hI).symm w) =
      ((h.quotientAlgEquiv hA fun x hx ↦ hI x (Ideal.IsPrime.le_of_pow_le hx)).trans
        (Ideal.quotientEquivAlgOfEq K (Ideal.map_pow φ I n))).symm
          (evalₐ (I.map φ) n w) := by
  simp only [completionAlgEquiv, AlgEquiv.ofAlgHom_symm_apply, evalₐ_liftAlgHom,
    AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgHom.restrictScalars_apply]

/-- At a point of an affinoid subdomain, restriction identifies the completions at the
corresponding maximal ideals. The extended ideal is maximal by `isMaximal_map`. -/
noncomputable def completionMaximalAlgEquiv {x : MaximalSpectrum A} (hx : x ∈ U) :
    AdicCompletion x.asIdeal A ≃ₐ[K] AdicCompletion (x.asIdeal.map φ) B :=
  h.completionAlgEquiv hA fun y hy ↦ by
    rwa [← MaximalSpectrum.ext (x.isMaximal.eq_of_le y.isMaximal.ne_top hy)]

/-- The maximal-ideal comparison specializes the supported-ideal comparison. -/
@[simp]
theorem completionMaximalAlgEquiv_eq_completionAlgEquiv {x : MaximalSpectrum A}
    (hx : x ∈ U) :
    h.completionMaximalAlgEquiv hA hx =
      h.completionAlgEquiv hA (fun y hy ↦ by
        rwa [← MaximalSpectrum.ext (x.isMaximal.eq_of_le y.isMaximal.ne_top hy)]) :=
  (rfl)

end TauCeti.IsAffinoidSubdomainMap
