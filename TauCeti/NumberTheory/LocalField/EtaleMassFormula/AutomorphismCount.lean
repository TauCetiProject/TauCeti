/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.IntermediateField.NormalSubfield.Sum
public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.SubfieldCount
import TauCeti.FieldTheory.IntermediateField.Map
import TauCeti.FieldTheory.IsSepClosed

/-!
# Isomorphism-class sums over the unramified part

Let `K` be a nonarchimedean local field and `L` a finite subextension of `SeparableClosure K` with
residue degree `f = L.inertiaDegree`. By `IntermediateField.unramifiedExtension_inertiaDegree_le`,
`L` contains the canonical unramified extension `K_f = unramifiedExtension K (SeparableClosure K) f`
of degree `f`, which is Galois over `K` with Galois group of cardinality `f`
(`TauCeti.natCard_algEquiv_unramifiedExtension`), decomposing `#Aut_K(L)` and the `K_f`-classes in
the `K`-class of `L` (`IntermediateField.natCard_algEquiv_eq_mul` and
`IntermediateField.ncard_isomorphic_restrictScalars_mul_natCard_eq_inertiaDegree`).

Specializing the normal-subfield weighted class-sum relation
`TauCeti.mul_tsum_div_natCard_algEquiv_eq_of_le` to `U = K_f` relates sums of `w(M) / #Aut_K(M)`
over `K`-isomorphism representatives to sums of `w(E) / #Aut_{K_f}(E)` over `K_f`-isomorphism
representatives (`TauCeti.mul_tsum_div_natCard_algEquiv_eq_of_inertiaDegree_eq` and
`TauCeti.tsum_div_natCard_algEquiv_eq_inv_mul_of_inertiaDegree_eq`). Specializing further to
extensions of degree `f * e` and residue degree `f` identifies the `K_f`-isomorphism classes with
Serre's `σ_{K_f}(e)` (`TauCeti.tsum_div_natCard_algEquiv_eq_inv_mul_tsum_isRepresentativeSet` and
`TauCeti.tsum_one_div_natCard_algEquiv_eq_inv_mul_tsum_isRepresentativeSet`), and combining with
Serre's second mass formula over `K_f` yields the isomorphism-class mass formula by residue degree
(`TauCeti.tsum_one_div_natCard_algEquiv_mul_natCard_residueField_pow_discriminantExponent`):

`∑_{[M]_K} 1 / (#Aut_K(M) · q ^ d(M)) = 1 / (f · q ^ (f(e - 1)))`.

## Main results

* `TauCeti.mul_tsum_div_natCard_algEquiv_eq_of_inertiaDegree_eq` and
  `TauCeti.tsum_div_natCard_algEquiv_eq_inv_mul_of_inertiaDegree_eq`: weighted class-sum relation
  between `K`-classes and `K_f`-classes for any `K`-isomorphism-closed family of residue degree `f`.
* `TauCeti.tsum_div_natCard_algEquiv_eq_inv_mul_tsum_isRepresentativeSet` and
  `TauCeti.tsum_one_div_natCard_algEquiv_eq_inv_mul_tsum_isRepresentativeSet`: weighted and
  unweighted class-sum relations against `IsRepresentativeSet e R` over an unramified base `F`.
* `TauCeti.tsum_one_div_natCard_algEquiv_mul_natCard_residueField_pow_discriminantExponent`:
  isomorphism-class mass formula for extensions of degree `f * e` and residue degree `f`.

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density of
  number field discriminants*, IMRN **2007**, rnm052, §2.
* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036, Théorème 2.
* J.-P. Serre, *Local Fields*, Chapter III, §5.
-/

public section
noncomputable section

open ValuativeRel IntermediateField
open scoped ENNReal

/-! ### Weighted isomorphism-class sums over the unramified base -/

namespace TauCeti

section InertiaFamily

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **Weighted class-sum relation over the unramified base (multiplied form).** Let `S` be a set of
subextensions of `SeparableClosure K` closed under `K`-isomorphism whose members all have residue
degree `f ≠ 0`, and let `U = unramifiedExtension K (SeparableClosure K) f`. For any set `R_K` of
`K`-isomorphism representatives of `S`, any set `R_U` of `U`-isomorphism representatives of
`{E : IntermediateField U (SeparableClosure K) | E.restrictScalars K ∈ S}`, and any weight
`w : IntermediateField K (SeparableClosure K) → ℝ≥0∞` invariant under `K`-isomorphisms out of `S`,
`f · ∑'_{M ∈ R_K} w(M) / #Aut_K(M) = ∑'_{E ∈ R_U} w(E) / #Aut_U(E)`. -/
theorem mul_tsum_div_natCard_algEquiv_eq_of_inertiaDegree_eq {f : ℕ} (hf : f ≠ 0)
    {S R_K : Set (IntermediateField K (SeparableClosure K))}
    (hS_iso : ∀ {L M : IntermediateField K (SeparableClosure K)}, L ∈ S → (L ≃ₐ[K] M) → M ∈ S)
    (hS_deg : ∀ L ∈ S, L.inertiaDegree = f)
    (hRK_sub : R_K ⊆ S)
    (hRK : ∀ L ∈ S, ∃! M, M ∈ R_K ∧ Nonempty (L ≃ₐ[K] M))
    {R_U : Set (IntermediateField (unramifiedExtension K (SeparableClosure K) f)
      (SeparableClosure K))}
    (hRU_sub : ∀ E ∈ R_U, E.restrictScalars K ∈ S)
    (hRU : ∀ E : IntermediateField (unramifiedExtension K (SeparableClosure K) f)
      (SeparableClosure K), E.restrictScalars K ∈ S →
        ∃! F, F ∈ R_U ∧ Nonempty (E ≃ₐ[unramifiedExtension K (SeparableClosure K) f] F))
    (w : IntermediateField K (SeparableClosure K) → ℝ≥0∞)
    (hw : ∀ {L M : IntermediateField K (SeparableClosure K)}, L ∈ S → (L ≃ₐ[K] M) → w L = w M) :
    (f : ℝ≥0∞) * ∑' M : R_K, w M.val / Nat.card (M.val ≃ₐ[K] M.val) =
      ∑' E : R_U, w (E.val.restrictScalars K) /
        Nat.card (E.val ≃ₐ[unramifiedExtension K (SeparableClosure K) f] E.val) := by
  let U := unramifiedExtension K (SeparableClosure K) f
  have hRK_le : ∀ M ∈ R_K, U ≤ M := by
    intro M hM
    have hMdeg : M.inertiaDegree = f := hS_deg M (hRK_sub hM)
    have : Module.Finite K M := by
      by_contra h
      exact hf (hMdeg.symm.trans (M.inertiaDegree_eq_zero_iff.2 h))
    simpa [U, hMdeg] using M.unramifiedExtension_inertiaDegree_le
  have hmul := mul_tsum_div_natCard_algEquiv_eq_of_le hS_iso hRK_le hRK_sub hRK hRU_sub hRU w hw
  rwa [natCard_algEquiv_unramifiedExtension hf] at hmul

/-- **Weighted class-sum relation over the unramified base.** Divided form of
`TauCeti.mul_tsum_div_natCard_algEquiv_eq_of_inertiaDegree_eq`:
`∑'_{M ∈ R_K} w(M) / #Aut_K(M) = f⁻¹ · ∑'_{E ∈ R_U} w(E) / #Aut_U(E)`. -/
theorem tsum_div_natCard_algEquiv_eq_inv_mul_of_inertiaDegree_eq {f : ℕ} (hf : f ≠ 0)
    {S R_K : Set (IntermediateField K (SeparableClosure K))}
    (hS_iso : ∀ {L M : IntermediateField K (SeparableClosure K)}, L ∈ S → (L ≃ₐ[K] M) → M ∈ S)
    (hS_deg : ∀ L ∈ S, L.inertiaDegree = f)
    (hRK_sub : R_K ⊆ S)
    (hRK : ∀ L ∈ S, ∃! M, M ∈ R_K ∧ Nonempty (L ≃ₐ[K] M))
    {R_U : Set (IntermediateField (unramifiedExtension K (SeparableClosure K) f)
      (SeparableClosure K))}
    (hRU_sub : ∀ E ∈ R_U, E.restrictScalars K ∈ S)
    (hRU : ∀ E : IntermediateField (unramifiedExtension K (SeparableClosure K) f)
      (SeparableClosure K), E.restrictScalars K ∈ S →
        ∃! F, F ∈ R_U ∧ Nonempty (E ≃ₐ[unramifiedExtension K (SeparableClosure K) f] F))
    (w : IntermediateField K (SeparableClosure K) → ℝ≥0∞)
    (hw : ∀ {L M : IntermediateField K (SeparableClosure K)}, L ∈ S → (L ≃ₐ[K] M) → w L = w M) :
    ∑' M : R_K, w M.val / Nat.card (M.val ≃ₐ[K] M.val) =
      (f : ℝ≥0∞)⁻¹ * ∑' E : R_U, w (E.val.restrictScalars K) /
        Nat.card (E.val ≃ₐ[unramifiedExtension K (SeparableClosure K) f] E.val) := by
  rw [← mul_tsum_div_natCard_algEquiv_eq_of_inertiaDegree_eq hf hS_iso hS_deg hRK_sub hRK
      hRU_sub hRU w hw,
    ← mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast hf) (ENNReal.natCast_ne_top _),
    one_mul]

end InertiaFamily

/-! ### Specialization to totally ramified extensions over an unramified base -/

section TotallyRamifiedTransport

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra K F] [ValuativeExtension K F] [IsUnramified K F]

section Embedded

variable [Algebra F (SeparableClosure K)] [IsScalarTower K F (SeparableClosure K)]

/-- Transporting intermediate fields of `SeparableClosure F / F` along
`Φ : SeparableClosure F ≃ₐ[F] SeparableClosure K` and `orderIsoOfFieldRangeEq` identifies them
order-isomorphically with intermediate fields of `SeparableClosure K` over
`unramifiedExtension K (SeparableClosure K) (TauCeti.inertiaDegree K F)`. -/
private def unramifiedTransportOrderIso (Φ : SeparableClosure F ≃ₐ[F] SeparableClosure K) :
    IntermediateField F (SeparableClosure F) ≃o
      IntermediateField
        (unramifiedExtension K (SeparableClosure K) (TauCeti.inertiaDegree K F))
        (SeparableClosure K) :=
  (orderIsoMapComap Φ).trans <|
    orderIsoOfFieldRangeEq
      (IsScalarTower.toAlgHom K F (SeparableClosure K)).fieldRange_eq_unramifiedExtension

private theorem unramifiedTransportOrderIso_apply
    (Φ : SeparableClosure F ≃ₐ[F] SeparableClosure K)
    (E : IntermediateField F (SeparableClosure F)) :
    unramifiedTransportOrderIso F Φ E =
      orderIsoOfFieldRangeEq
        (IsScalarTower.toAlgHom K F (SeparableClosure K)).fieldRange_eq_unramifiedExtension
        (E.map Φ.toAlgHom) := by
  rw [unramifiedTransportOrderIso, OrderIso.trans_apply, orderIsoMapComap_apply]

private theorem restrictScalars_unramifiedTransportOrderIso
    (Φ : SeparableClosure F ≃ₐ[F] SeparableClosure K)
    (E : IntermediateField F (SeparableClosure F)) :
    (unramifiedTransportOrderIso F Φ E).restrictScalars K =
      (E.map Φ.toAlgHom).restrictScalars K := by
  rw [unramifiedTransportOrderIso_apply, restrictScalars_orderIsoOfFieldRangeEq]

/-- Under `unramifiedTransportOrderIso F Φ`, `F`-algebra equivalences `E₁ ≃ₐ[F] E₂` correspond to
`unramifiedExtension K (SeparableClosure K) (TauCeti.inertiaDegree K F)`-algebra equivalences
between the transported intermediate fields. -/
private def unramifiedTransportAlgEquivEquiv (Φ : SeparableClosure F ≃ₐ[F] SeparableClosure K)
    (E₁ E₂ : IntermediateField F (SeparableClosure F)) :
    (E₁ ≃ₐ[F] E₂) ≃
      (unramifiedTransportOrderIso F Φ E₁ ≃ₐ[
        unramifiedExtension K (SeparableClosure K) (TauCeti.inertiaDegree K F)]
        unramifiedTransportOrderIso F Φ E₂) :=
  ((intermediateFieldMap Φ E₁).equivCongr (intermediateFieldMap Φ E₂)).trans <|
    (algEquivEquivOfFieldRangeEq
        (IsScalarTower.toAlgHom K F (SeparableClosure K)).fieldRange_eq_unramifiedExtension
        (E₁.map Φ.toAlgHom) (E₂.map Φ.toAlgHom)).trans <|
      (equivOfEq (unramifiedTransportOrderIso_apply F Φ E₁).symm).equivCongr
        (equivOfEq (unramifiedTransportOrderIso_apply F Φ E₂).symm)

private theorem image_unramifiedTransportOrderIso_subset {e : ℕ}
    (Φ : SeparableClosure F ≃ₐ[F] SeparableClosure K)
    {R : Set (IntermediateField F (SeparableClosure F))} (hR : IsRepresentativeSet e R) :
    ∀ N ∈ unramifiedTransportOrderIso F Φ '' R,
      N.restrictScalars K ∈
        {L : IntermediateField K (SeparableClosure K) |
          Module.finrank K L = TauCeti.inertiaDegree K F * e ∧
            L.inertiaDegree = TauCeti.inertiaDegree K F} := by
  rintro _ ⟨M, hM, rfl⟩
  have hmem : (M.map Φ.toAlgHom).map Φ.symm.toAlgHom ∈ totallyRamifiedOfDegree F e := by
    rw [map_symm_map]
    exact hR.subset hM
  have h := (map_mem_totallyRamifiedOfDegree_iff F Φ (M.map Φ.toAlgHom) e).1 hmem
  rw [← IsUnramified.inertiaDegree_eq_finrank (K := K) (L := F)] at h
  rw [restrictScalars_unramifiedTransportOrderIso]
  exact h

private theorem existsUnique_mem_image_unramifiedTransportOrderIso {e : ℕ}
    (Φ : SeparableClosure F ≃ₐ[F] SeparableClosure K)
    {R : Set (IntermediateField F (SeparableClosure F))} (hR : IsRepresentativeSet e R)
    (N : IntermediateField
      (unramifiedExtension K (SeparableClosure K) (TauCeti.inertiaDegree K F))
      (SeparableClosure K))
    (hN : N.restrictScalars K ∈
      {L : IntermediateField K (SeparableClosure K) |
        Module.finrank K L = TauCeti.inertiaDegree K F * e ∧
          L.inertiaDegree = TauCeti.inertiaDegree K F}) :
    ∃! P, P ∈ unramifiedTransportOrderIso F Φ '' R ∧
      Nonempty
        (N ≃ₐ[unramifiedExtension K (SeparableClosure K) (TauCeti.inertiaDegree K F)] P) := by
  let hU := (IsScalarTower.toAlgHom K F (SeparableClosure K)).fieldRange_eq_unramifiedExtension
  let θ := unramifiedTransportOrderIso F Φ
  let E₀ : IntermediateField F (SeparableClosure K) := (orderIsoOfFieldRangeEq hU).symm N
  let M₀ : IntermediateField F (SeparableClosure F) := θ.symm N
  have hN_eq : θ M₀ = N := θ.apply_symm_apply N
  have hsymm : M₀ = E₀.map Φ.symm.toAlgHom := by
    dsimp only [M₀, θ, E₀]
    rw [unramifiedTransportOrderIso, OrderIso.symm_trans_apply, orderIsoMapComap_symm_apply']
  have hE₀' : E₀.restrictScalars K ∈
      {L : IntermediateField K (SeparableClosure K) |
        Module.finrank K L = TauCeti.inertiaDegree K F * e ∧
          L.inertiaDegree = TauCeti.inertiaDegree K F} := by
    rwa [restrictScalars_orderIsoOfFieldRangeEq_symm hU N]
  have hE₀ : Module.finrank K (E₀.restrictScalars K) = Module.finrank K F * e ∧
      (E₀.restrictScalars K).inertiaDegree = TauCeti.inertiaDegree K F := by
    rw [← IsUnramified.inertiaDegree_eq_finrank (K := K) (L := F)]
    exact hE₀'
  have hmem : M₀ ∈ totallyRamifiedOfDegree F e := by
    rw [hsymm]
    exact (map_mem_totallyRamifiedOfDegree_iff F Φ E₀ e).2 hE₀
  obtain ⟨M, ⟨hMR, hisoM⟩, huniq⟩ := hR.existsUnique hmem
  have hbij (M' : IntermediateField F (SeparableClosure F)) :
      Nonempty
          (N ≃ₐ[unramifiedExtension K (SeparableClosure K) (TauCeti.inertiaDegree K F)] θ M') ↔
        Nonempty (M₀ ≃ₐ[F] M') := by
    rw [← hN_eq]
    exact (unramifiedTransportAlgEquivEquiv F Φ M₀ M').symm.nonempty_congr
  refine ⟨θ M, ⟨⟨M, hMR, rfl⟩, (hbij M).2 hisoM⟩, ?_⟩
  rintro _ ⟨⟨M', hM'R, rfl⟩, hN'⟩
  exact congrArg θ (huniq M' ⟨hM'R, (hbij M').1 hN'⟩)

/-- **Weighted isomorphism-class sum by residue degree ([Bhargava 2007, §2]).** Let `F` be an
unramified extension of `K` embedded in `SeparableClosure K` with residue degree `f = f(F / K)`.
For every set `R_K` of `K`-isomorphism representatives of the subextensions of degree `f * e` and
residue degree `f`, every set `R` of `F`-isomorphism representatives of `σ_F(e)`, every
`Φ : SeparableClosure F ≃ₐ[F] SeparableClosure K`, and every weight `w` invariant under
`K`-isomorphisms out of `{L | [L : K] = f * e ∧ L.inertiaDegree = f}`,
`∑'_{M ∈ R_K} w(M) / #Aut_K(M) = f⁻¹ · ∑'_{E ∈ R} w((E.map Φ).restrictScalars K) / #Aut_F(E)`. -/
theorem tsum_div_natCard_algEquiv_eq_inv_mul_tsum_isRepresentativeSet {e : ℕ}
    (Φ : SeparableClosure F ≃ₐ[F] SeparableClosure K)
    {R_K : Set (IntermediateField K (SeparableClosure K))}
    (hRK_sub : R_K ⊆ {L | Module.finrank K L = TauCeti.inertiaDegree K F * e ∧
      L.inertiaDegree = TauCeti.inertiaDegree K F})
    (hRK : ∀ L : IntermediateField K (SeparableClosure K),
      Module.finrank K L = TauCeti.inertiaDegree K F * e ∧
        L.inertiaDegree = TauCeti.inertiaDegree K F →
        ∃! M, M ∈ R_K ∧ Nonempty (L ≃ₐ[K] M))
    {R : Set (IntermediateField F (SeparableClosure F))}
    (hR : IsRepresentativeSet e R)
    (w : IntermediateField K (SeparableClosure K) → ℝ≥0∞)
    (hw : ∀ {L M : IntermediateField K (SeparableClosure K)},
      Module.finrank K L = TauCeti.inertiaDegree K F * e ∧
        L.inertiaDegree = TauCeti.inertiaDegree K F →
        (L ≃ₐ[K] M) → w L = w M) :
    ∑' M : R_K, w M.val / Nat.card (M.val ≃ₐ[K] M.val) =
      (TauCeti.inertiaDegree K F : ℝ≥0∞)⁻¹ * ∑' E : R,
        w ((E.val.map Φ.toAlgHom).restrictScalars K) / Nat.card (E.val ≃ₐ[F] E.val) := by
  have hf : TauCeti.inertiaDegree K F ≠ 0 := TauCeti.inertiaDegree_pos.ne'
  let S : Set (IntermediateField K (SeparableClosure K)) :=
    {L | Module.finrank K L = TauCeti.inertiaDegree K F * e ∧
      L.inertiaDegree = TauCeti.inertiaDegree K F}
  have hS_iso :
      ∀ {L M : IntermediateField K (SeparableClosure K)}, L ∈ S → (L ≃ₐ[K] M) → M ∈ S :=
    fun ⟨hr, hi⟩ e₀ ↦ ⟨e₀.toLinearEquiv.finrank_eq.symm.trans hr,
      (IntermediateField.inertiaDegree_eq_of_algEquiv e₀).symm.trans hi⟩
  -- Relate the `K`-class sum to the `U`-class sum over `θ '' R`, then pull back along `θ` to `R`.
  rw [tsum_div_natCard_algEquiv_eq_inv_mul_of_inertiaDegree_eq hf hS_iso (fun _ hL ↦ hL.2)
      hRK_sub hRK (image_unramifiedTransportOrderIso_subset F Φ hR)
      (existsUnique_mem_image_unramifiedTransportOrderIso F Φ hR) w hw]
  set θ := unramifiedTransportOrderIso F Φ
  congr 1
  rw [← OrderIso.coe_toEquiv θ, ← (Equiv.Set.image θ.toEquiv R θ.injective).tsum_eq]
  refine tsum_congr fun E ↦ ?_
  have hcard :
      Nat.card (θ E.val ≃ₐ[
          unramifiedExtension K (SeparableClosure K) (TauCeti.inertiaDegree K F)] θ E.val) =
        Nat.card (E.val ≃ₐ[F] E.val) :=
    Nat.card_congr (unramifiedTransportAlgEquivEquiv F Φ E.val E.val).symm
  rw [Equiv.Set.image_apply, OrderIso.coe_toEquiv, Subtype.coe_mk, hcard,
    restrictScalars_unramifiedTransportOrderIso]

end Embedded

/-- **Unweighted isomorphism-class sum over an unramified base.** With `w = 1`, the sum of
`1 / #Aut_K(M)` over `K`-isomorphism classes of degree `f(F / K) * e` and residue degree
`f(F / K)` equals `f(F / K)⁻¹` times the sum of `1 / #Aut_F(E)` over `F`-isomorphism classes in
`σ_F(e)`. -/
theorem tsum_one_div_natCard_algEquiv_eq_inv_mul_tsum_isRepresentativeSet {e : ℕ}
    {R_K : Set (IntermediateField K (SeparableClosure K))}
    (hRK_sub : R_K ⊆ {L | Module.finrank K L = TauCeti.inertiaDegree K F * e ∧
      L.inertiaDegree = TauCeti.inertiaDegree K F})
    (hRK : ∀ L : IntermediateField K (SeparableClosure K),
      Module.finrank K L = TauCeti.inertiaDegree K F * e ∧
        L.inertiaDegree = TauCeti.inertiaDegree K F →
        ∃! M, M ∈ R_K ∧ Nonempty (L ≃ₐ[K] M))
    {R : Set (IntermediateField F (SeparableClosure F))}
    (hR : IsRepresentativeSet e R) :
    ∑' M : R_K, 1 / (Nat.card (M.val ≃ₐ[K] M.val) : ℝ≥0∞) =
      (TauCeti.inertiaDegree K F : ℝ≥0∞)⁻¹ *
        ∑' E : R, 1 / (Nat.card (E.val ≃ₐ[F] E.val) : ℝ≥0∞) := by
  have : IsGalois K F := IsUnramified.isGalois K F
  let ι : F →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let _ := ι.toAlgebra
  have : IsScalarTower K F (SeparableClosure K) := .of_algebraMap_eq fun x ↦ (ι.commutes x).symm
  have := isSepClosure_tower_top K F (SeparableClosure K)
  let Φ := IsSepClosure.equiv F (SeparableClosure F) (SeparableClosure K)
  exact tsum_div_natCard_algEquiv_eq_inv_mul_tsum_isRepresentativeSet F Φ hRK_sub hRK hR
    (fun _ ↦ 1) (fun _ _ ↦ rfl)

/-- Serre's second mass formula read over `K` via an unramified extension `F`. -/
private theorem tsum_one_div_natCard_algEquiv_mul_natCard_residueField_pow_discriminantExponent_aux
    {e : ℕ} (he : 0 < e)
    {R_K : Set (IntermediateField K (SeparableClosure K))}
    (hRK_sub : R_K ⊆ {L | Module.finrank K L = TauCeti.inertiaDegree K F * e ∧
      L.inertiaDegree = TauCeti.inertiaDegree K F})
    (hRK : ∀ L : IntermediateField K (SeparableClosure K),
      Module.finrank K L = TauCeti.inertiaDegree K F * e ∧
        L.inertiaDegree = TauCeti.inertiaDegree K F →
        ∃! M, M ∈ R_K ∧ Nonempty (L ≃ₐ[K] M)) :
    ∑' M : R_K, 1 / ((Nat.card (M.val ≃ₐ[K] M.val) : ℝ≥0∞) *
        (Nat.card 𝓀[K] : ℝ≥0∞) ^ M.val.discriminantExponent) =
      1 / ((TauCeti.inertiaDegree K F : ℝ≥0∞) *
        (Nat.card 𝓀[K] : ℝ≥0∞) ^ (TauCeti.inertiaDegree K F * (e - 1))) := by
  have : IsGalois K F := IsUnramified.isGalois K F
  let ι : F →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let _ := ι.toAlgebra
  have : IsScalarTower K F (SeparableClosure K) := .of_algebraMap_eq fun x ↦ (ι.commutes x).symm
  have := isSepClosure_tower_top K F (SeparableClosure K)
  let Φ := IsSepClosure.equiv F (SeparableClosure F) (SeparableClosure K)
  obtain ⟨R, hR⟩ := exists_isRepresentativeSet F e
  have hrel := tsum_div_natCard_algEquiv_eq_inv_mul_tsum_isRepresentativeSet F Φ hRK_sub hRK hR
    (fun L ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.discriminantExponent)
    (fun _ e₀ ↦ by rw [IntermediateField.discriminantExponent_eq_of_algEquiv e₀])
  have hLHS (M : R_K) :
      1 / ((Nat.card (M.val ≃ₐ[K] M.val) : ℝ≥0∞) *
          (Nat.card 𝓀[K] : ℝ≥0∞) ^ M.val.discriminantExponent) =
        (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ M.val.discriminantExponent) /
          Nat.card (M.val ≃ₐ[K] M.val) := by
    rw [one_div, one_div, div_eq_mul_inv,
      ENNReal.mul_inv (.inr (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))
        (.inl (ENNReal.natCast_ne_top _)), mul_comm]
  have hRHS (E : R) :
      (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^
          ((E.val.map Φ.toAlgHom).restrictScalars K).discriminantExponent) /
          Nat.card (E.val ≃ₐ[F] E.val) =
        1 / ((Nat.card (E.val ≃ₐ[F] E.val) : ℝ≥0∞) *
            (Nat.card 𝓀[F] : ℝ≥0∞) ^ E.val.wildExponent) *
          (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (TauCeti.inertiaDegree K F * (e - 1))) := by
    have hmem : (E.val.map Φ.toAlgHom).map Φ.symm.toAlgHom ∈ totallyRamifiedOfDegree F e := by
      rw [map_symm_map]
      exact hR.subset E.property
    have hdisc := one_div_natCard_residueField_pow_discriminantExponent_restrictScalars F Φ
      (E.val.map Φ.toAlgHom) hmem
    rw [map_symm_map] at hdisc
    rw [hdisc, div_eq_mul_inv, one_div, one_div, one_div,
      ENNReal.mul_inv (.inr (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))
        (.inl (ENNReal.natCast_ne_top _)), mul_comm, ← mul_assoc]
  rw [tsum_congr hLHS, hrel, tsum_congr hRHS, ENNReal.tsum_mul_right,
    hR.tsum_one_div_natCard_algEquiv_mul_natCard_residueField_pow_wildExponent he, one_mul,
    one_div, one_div,
    ENNReal.mul_inv (.inr (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))
      (.inl (ENNReal.natCast_ne_top _))]

end TotallyRamifiedTransport

/-- **Isomorphism-class mass formula by residue degree ([Bhargava 2007, §2]).** For `f ≠ 0`,
`0 < e`, and every set `R_K` of `K`-isomorphism representatives of the subextensions of
`SeparableClosure K` of degree `f * e` and residue degree `f` (such sets always exist by
`IntermediateField.exists_subset_existsUnique_algEquiv`),
`∑'_{M ∈ R_K} 1 / (#Aut_K(M) · q ^ d(M)) = 1 / (f · q ^ (f(e - 1)))`,
deduced from Serre's second mass formula over `K_f` via the weighted class-sum relation. -/
theorem tsum_one_div_natCard_algEquiv_mul_natCard_residueField_pow_discriminantExponent
    {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {f e : ℕ} (hf : f ≠ 0) (he : 0 < e)
    {R_K : Set (IntermediateField K (SeparableClosure K))}
    (hRK_sub : R_K ⊆ {L | Module.finrank K L = f * e ∧ L.inertiaDegree = f})
    (hRK : ∀ L : IntermediateField K (SeparableClosure K),
      Module.finrank K L = f * e ∧ L.inertiaDegree = f → ∃! M, M ∈ R_K ∧ Nonempty (L ≃ₐ[K] M)) :
    ∑' M : R_K, 1 / ((Nat.card (M.val ≃ₐ[K] M.val) : ℝ≥0∞) *
        (Nat.card 𝓀[K] : ℝ≥0∞) ^ M.val.discriminantExponent) =
      1 / ((f : ℝ≥0∞) * (Nat.card 𝓀[K] : ℝ≥0∞) ^ (f * (e - 1))) := by
  set U := unramifiedExtension K (SeparableClosure K) f
  let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) U
  let _ := finiteIntermediateFieldTopology K (SeparableClosure K) U
  have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) U
  have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) U
  have : IsUnramified K U := isUnramified_unramifiedExtension
  have hUf : TauCeti.inertiaDegree K U = f := by
    rw [IsUnramified.inertiaDegree_eq_finrank, finrank_unramifiedExtension hf]
  have hRK_sub' : R_K ⊆ {L | Module.finrank K L = TauCeti.inertiaDegree K U * e ∧
      L.inertiaDegree = TauCeti.inertiaDegree K U} := by
    rwa [hUf]
  have hRK' : ∀ L : IntermediateField K (SeparableClosure K),
      Module.finrank K L = TauCeti.inertiaDegree K U * e ∧
        L.inertiaDegree = TauCeti.inertiaDegree K U →
        ∃! M, M ∈ R_K ∧ Nonempty (L ≃ₐ[K] M) := by
    rwa [hUf]
  have h :=
    tsum_one_div_natCard_algEquiv_mul_natCard_residueField_pow_discriminantExponent_aux U he
      hRK_sub' hRK'
  rwa [hUf] at h

end TauCeti
