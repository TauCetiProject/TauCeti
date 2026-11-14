/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.IntermediateField.NormalSubfield
public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.SubfieldCount
import TauCeti.FieldTheory.IntermediateField.Map
import TauCeti.FieldTheory.IsSepClosed

/-!
# The automorphism count and isomorphism-class sums over the unramified part

Let `K` be a nonarchimedean local field and `L` a finite subextension of `SeparableClosure K` with
residue degree `f = L.inertiaDegree`. By `IntermediateField.unramifiedExtension_inertiaDegree_le`,
`L` contains the canonical unramified extension `K_f = unramifiedExtension K (SeparableClosure K) f`
of degree `f`, which is Galois over `K`.

Restricting automorphisms in `L ≃ₐ[K] L` to `K_f` therefore yields a group homomorphism whose
kernel is the `K_f`-automorphism group of `extendScalars L.unramifiedExtension_inertiaDegree_le`
and whose image consists of the automorphisms of `K_f / K` that extend to `L`. This gives the
automorphism decomposition (`IntermediateField.natCard_algEquiv_eq_mul`)

`#Aut_K(L) = #Aut_{K_f}(L) · #{τ ∈ Gal(K_f / K) | τ extends to L}`.

More generally, over any normal extension `Ω / K` and normal intermediate field `U / K` with
finitely many `K`-automorphisms, the `U`-isomorphism classes whose underlying `K`-field is
`K`-isomorphic to `M` (for `U ≤ M`) form an orbit of size `#Aut_K(U) / #{τ | τ extends to M}`, each
having `#Aut_U(M)` automorphisms over `U`. Summing a `K`-isomorphism-invariant weight `w` valued in
`ℝ≥0∞` over `U`-isomorphism representatives therefore multiplies the corresponding sum over
`K`-isomorphism representatives by `#Aut_K(U)` (`TauCeti.mul_tsum_div_natCard_algEquiv_eq_of_le`).

For `U = K_f` this gives `#Aut_K(U) = f`
(`TauCeti.mul_tsum_div_natCard_algEquiv_eq_of_inertiaDegree_eq` and
`TauCeti.tsum_div_natCard_algEquiv_eq_inv_mul_of_inertiaDegree_eq`). Specializing to the
extensions of degree `f * e` and residue degree `f` identifies the `K_f`-isomorphism classes with
Serre's `σ_{K_f}(e)` (`TauCeti.tsum_div_natCard_algEquiv_eq_inv_mul_tsum_isRepresentativeSet` and
`TauCeti.tsum_one_div_natCard_algEquiv_eq_inv_mul_tsum_isRepresentativeSet`), and combining with
Serre's second mass formula over `K_f` yields the isomorphism-class mass formula by residue degree
(`TauCeti.tsum_one_div_natCard_algEquiv_mul_natCard_residueField_pow_discriminantExponent`):

`∑_{[M]_K} 1 / (#Aut_K(M) · q ^ d(M)) = 1 / (f · q ^ (f(e - 1)))`.

## Main results

* `IntermediateField.natCard_algEquiv_eq_mul`: decomposition of `Nat.card (L ≃ₐ[K] L)` along the
  unramified part `K_{f(L/K)} ≤ L`.
* `IntermediateField.natCard_algEquiv_eq_mul_inertiaDegree_of_normal`: for normal `L / K`, every
  automorphism of `K_{f(L/K)} / K` extends, so `#Aut_K(L) = #Aut_{K_f}(L) · f(L / K)`.
* `IntermediateField.natCard_algEquiv_eq_of_isTotallyRamified`: for totally ramified `L / K`,
  `#Aut_K(L) = #Aut_{K_1}(L)`.
* `TauCeti.mul_tsum_div_natCard_algEquiv_eq_of_le` and
  `TauCeti.tsum_div_natCard_algEquiv_eq_inv_mul_of_le`: weighted class-sum relation over any normal
  intermediate field `U / K` with `Finite (U ≃ₐ[K] U)` inside a normal ambient extension `Ω / K`.
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

open ValuativeRel IntermediateField TauCeti
open scoped ENNReal

/-! ### The automorphism count of a finite subextension -/

namespace IntermediateField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **The automorphism count over the unramified part**: for a finite subextension `L` of
`SeparableClosure K` with residue degree `f = L.inertiaDegree` and canonical unramified base
`U = unramifiedExtension K (SeparableClosure K) f`, restriction `Aut_K(L) → Gal(U / K)` has kernel
`Aut_U(L)` and image the automorphisms of `U / K` that extend to `L`. -/
theorem natCard_algEquiv_eq_mul (L : IntermediateField K (SeparableClosure K))
    [Module.Finite K L] :
    Nat.card (L ≃ₐ[K] L) =
      Nat.card (extendScalars L.unramifiedExtension_inertiaDegree_le ≃ₐ[
          unramifiedExtension K (SeparableClosure K) L.inertiaDegree]
          extendScalars L.unramifiedExtension_inertiaDegree_le) *
        Nat.card {τ : unramifiedExtension K (SeparableClosure K) L.inertiaDegree ≃ₐ[K]
            unramifiedExtension K (SeparableClosure K) L.inertiaDegree //
          ∃ σ : L ≃ₐ[K] L, ∀ x,
            (σ ⟨x.1, L.unramifiedExtension_inertiaDegree_le x.2⟩ :
              SeparableClosure K) = τ x} :=
  natCard_algEquiv_eq_mul_of_le L.unramifiedExtension_inertiaDegree_le

/-- When `L` is finite and normal over `K`, every automorphism of its unramified part extends to
`L`, so `#Aut_K(L) = #Aut_U(extendScalars L.unramifiedExtension_inertiaDegree_le) · f(L / K)`. -/
theorem natCard_algEquiv_eq_mul_inertiaDegree_of_normal
    (L : IntermediateField K (SeparableClosure K)) [Module.Finite K L] [Normal K L] :
    Nat.card (L ≃ₐ[K] L) =
      Nat.card (extendScalars L.unramifiedExtension_inertiaDegree_le ≃ₐ[
          unramifiedExtension K (SeparableClosure K) L.inertiaDegree]
          extendScalars L.unramifiedExtension_inertiaDegree_le) *
        L.inertiaDegree := by
  have hU : Nat.card (unramifiedExtension K (SeparableClosure K) L.inertiaDegree ≃ₐ[K]
      unramifiedExtension K (SeparableClosure K) L.inertiaDegree) = L.inertiaDegree :=
    (IsGalois.card_aut_eq_finrank _ _).trans (finrank_unramifiedExtension L.inertiaDegree_pos.ne')
  rw [natCard_algEquiv_eq_mul_of_normal L.unramifiedExtension_inertiaDegree_le, hU]

/-- When `L` is totally ramified over `K`, its unramified part has degree `1` over `K`, so every
`K`-automorphism of `L` fixes its unramified part pointwise. -/
theorem natCard_algEquiv_eq_of_isTotallyRamified
    (L : IntermediateField K (SeparableClosure K)) [Module.Finite K L]
    (hL : L.IsTotallyRamified) :
    Nat.card (L ≃ₐ[K] L) =
      Nat.card (extendScalars L.unramifiedExtension_inertiaDegree_le ≃ₐ[
          unramifiedExtension K (SeparableClosure K) L.inertiaDegree]
          extendScalars L.unramifiedExtension_inertiaDegree_le) := by
  let U := unramifiedExtension K (SeparableClosure K) L.inertiaDegree
  have hUcard : Nat.card (U ≃ₐ[K] U) = 1 := by
    rw [IsGalois.card_aut_eq_finrank, finrank_unramifiedExtension L.inertiaDegree_pos.ne',
      L.isTotallyRamified_iff_inertiaDegree_eq_one.1 hL]
  have : Subsingleton (U ≃ₐ[K] U) := (Nat.card_eq_one_iff_unique.1 hUcard).1
  have hsub : Nat.card {τ : U ≃ₐ[K] U //
      ∃ σ : L ≃ₐ[K] L, ∀ x,
        (σ ⟨x.1, L.unramifiedExtension_inertiaDegree_le x.2⟩ : SeparableClosure K) = τ x} = 1 := by
    refine Nat.card_eq_one_iff_exists.2 ⟨⟨1, ⟨.refl, fun _ ↦ rfl⟩⟩, fun ⟨τ, _⟩ ↦ ?_⟩
    exact Subtype.ext (Subsingleton.elim τ 1)
  rw [L.natCard_algEquiv_eq_mul, hsub, mul_one]

end IntermediateField

/-! ### Weighted isomorphism-class sums over a normal intermediate field -/

namespace TauCeti

section NormalSubfieldSum

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [Normal K Ω]

/-- On a single `K`-isomorphism class representative `M` containing a normal intermediate field `U`
with `Finite (U ≃ₐ[K] U)`, summing `w(E) / #Aut_U(E)` over the `U`-isomorphism representatives
`E ∈ R_U` lying in the `K`-class of `M` gives `#Aut_K(U) · (w(M) / #Aut_K(M))`: there are
`#Aut_K(U) / #Stab(M)` such `U`-classes, each with `#Aut_U(M)` automorphisms over `U`, and
`#Aut_K(M) = #Aut_U(M) · #Stab(M)`. -/
private theorem tsum_fiber_div_natCard_algEquiv_eq {U M : IntermediateField K Ω} [Normal K U]
    [Finite (U ≃ₐ[K] U)] (hUM : U ≤ M) {R_U : Set (IntermediateField U Ω)}
    (hRU : ∀ E : IntermediateField U Ω, Nonempty (M ≃ₐ[K] E.restrictScalars K) →
      ∃! F, F ∈ R_U ∧ Nonempty (E ≃ₐ[U] F))
    (w : IntermediateField K Ω → ℝ≥0∞)
    (hw : ∀ {L₁ L₂ : IntermediateField K Ω}, (L₁ ≃ₐ[K] L₂) → w L₁ = w L₂) :
    ∑' E : {E ∈ R_U | Nonempty (M ≃ₐ[K] E.restrictScalars K)},
        w (E.1.restrictScalars K) / Nat.card (E.1 ≃ₐ[U] E.1) =
      (Nat.card (U ≃ₐ[K] U) : ℝ≥0∞) * (w M / Nat.card (M ≃ₐ[K] M)) := by
  let C : Set (IntermediateField U Ω) := {E ∈ R_U | Nonempty (M ≃ₐ[K] E.restrictScalars K)}
  have hU_ne : Nat.card (U ≃ₐ[K] U) ≠ 0 := Nat.card_ne_zero.2 ⟨⟨1⟩, inferInstance⟩
  have horbit : C.ncard * Nat.card {τ : U ≃ₐ[K] U //
      ∃ σ : M ≃ₐ[K] M, ∀ x : U, (σ ⟨x.1, hUM x.2⟩ : Ω) = τ x} = Nat.card (U ≃ₐ[K] U) :=
    ncard_isomorphic_restrictScalars_mul_natCard_eq hUM hRU
  have hAutM := natCard_algEquiv_eq_mul_of_le hUM
  have hs_ne : Nat.card {τ : U ≃ₐ[K] U //
      ∃ σ : M ≃ₐ[K] M, ∀ x : U, (σ ⟨x.1, hUM x.2⟩ : Ω) = τ x} ≠ 0 :=
    Nat.card_ne_zero.2 ⟨⟨⟨1, ⟨.refl, fun _ ↦ rfl⟩⟩⟩, inferInstance⟩
  have hC_fin : C.Finite :=
    Set.finite_of_ncard_ne_zero (left_ne_zero_of_mul (horbit.symm ▸ hU_ne))
  have hconst (E : C) :
      w (E.1.restrictScalars K) / Nat.card (E.1 ≃ₐ[U] E.1) =
        w M / Nat.card (extendScalars hUM ≃ₐ[U] extendScalars hUM) := by
    obtain ⟨e⟩ := E.2.2
    rw [(hw e).symm, (natCard_extendScalars_algEquiv_eq_of_algEquiv_restrictScalars hUM e).symm]
  rw [tsum_congr hconst, ENNReal.tsum_set_const, ← hC_fin.cast_ncard_eq]
  set a : ℝ≥0∞ := (Nat.card (extendScalars hUM ≃ₐ[U] extendScalars hUM) : ℝ≥0∞)
  set s : ℝ≥0∞ := (Nat.card {τ : U ≃ₐ[K] U //
    ∃ σ : M ≃ₐ[K] M, ∀ x : U, (σ ⟨x.1, hUM x.2⟩ : Ω) = τ x} : ℝ≥0∞)
  have ha_top : a ≠ ⊤ := ENNReal.natCast_ne_top _
  have hs_top : s ≠ ⊤ := ENNReal.natCast_ne_top _
  have hs0 : s ≠ 0 := Nat.cast_ne_zero.2 hs_ne
  have hcs : (C.ncard : ℝ≥0∞) * s = Nat.card (U ≃ₐ[K] U) := by
    simp only [s, ← Nat.cast_mul, horbit]
  have has : (Nat.card (M ≃ₐ[K] M) : ℝ≥0∞) = a * s := by
    simp only [a, s, ← Nat.cast_mul, hAutM]
  rw [has]
  calc
    (C.ncard : ℝ≥0∞) * (w M / a)
      = (C.ncard : ℝ≥0∞) * (w M * a⁻¹) * 1 := by rw [div_eq_mul_inv, mul_one]
    _ = (C.ncard : ℝ≥0∞) * (w M * a⁻¹) * (s * s⁻¹) := by
          rw [ENNReal.mul_inv_cancel hs0 hs_top]
    _ = ((C.ncard : ℝ≥0∞) * s) * (w M * (a⁻¹ * s⁻¹)) := by ac_rfl
    _ = (Nat.card (U ≃ₐ[K] U) : ℝ≥0∞) * (w M / (a * s)) := by
          rw [hcs, ← ENNReal.mul_inv (.inr hs_top) (.inl ha_top), ← div_eq_mul_inv]

/-- **Weighted class-sum relation over a normal intermediate field.** Let `Ω / K` be normal and let
`U` be a normal intermediate field of `Ω / K` with `Finite (U ≃ₐ[K] U)`. For any
`K`-isomorphism-closed family `S` of intermediate fields of `Ω / K`, any set `R_K ⊆ S` of
`K`-isomorphism representatives of `S` with `U ≤ M` for all `M ∈ R_K`, any set `R_U` of
`U`-isomorphism representatives of `{E : IntermediateField U Ω | E.restrictScalars K ∈ S}`, and any
`K`-isomorphism-invariant weight `w : IntermediateField K Ω → ℝ≥0∞`,
`#Aut_K(U) · ∑'_{M ∈ R_K} w(M) / #Aut_K(M) = ∑'_{E ∈ R_U} w(E) / #Aut_U(E)`. -/
theorem mul_tsum_div_natCard_algEquiv_eq_of_le {U : IntermediateField K Ω} [Normal K U]
    [Finite (U ≃ₐ[K] U)] {S R_K : Set (IntermediateField K Ω)}
    (hS_iso : ∀ {L M : IntermediateField K Ω}, L ∈ S → (L ≃ₐ[K] M) → M ∈ S)
    (hRK_le : ∀ M ∈ R_K, U ≤ M)
    (hRK_sub : R_K ⊆ S)
    (hRK : ∀ L ∈ S, ∃! M, M ∈ R_K ∧ Nonempty (L ≃ₐ[K] M))
    {R_U : Set (IntermediateField U Ω)}
    (hRU_sub : ∀ E ∈ R_U, E.restrictScalars K ∈ S)
    (hRU : ∀ E : IntermediateField U Ω, E.restrictScalars K ∈ S →
      ∃! F, F ∈ R_U ∧ Nonempty (E ≃ₐ[U] F))
    (w : IntermediateField K Ω → ℝ≥0∞)
    (hw : ∀ {L M : IntermediateField K Ω}, (L ≃ₐ[K] M) → w L = w M) :
    (Nat.card (U ≃ₐ[K] U) : ℝ≥0∞) * ∑' M : R_K, w M.1 / Nat.card (M.1 ≃ₐ[K] M.1) =
      ∑' E : R_U, w (E.1.restrictScalars K) / Nat.card (E.1 ≃ₐ[U] E.1) := by
  let g (E : IntermediateField U Ω) : ℝ≥0∞ :=
    w (E.restrictScalars K) / Nat.card (E ≃ₐ[U] E)
  let C (M : IntermediateField K Ω) : Set (IntermediateField U Ω) :=
    {E ∈ R_U | Nonempty (M ≃ₐ[K] E.restrictScalars K)}
  have hU_eq : R_U = ⋃ M ∈ R_K, C M := by
    ext E
    simp only [Set.mem_iUnion, exists_prop, C]
    refine ⟨fun hE ↦ ?_, fun ⟨_, _, hE, _⟩ ↦ hE⟩
    obtain ⟨M, ⟨hM, ⟨e⟩⟩, -⟩ := hRK (E.restrictScalars K) (hRU_sub E hE)
    exact ⟨M, hM, hE, ⟨e.symm⟩⟩
  have hdisj : R_K.PairwiseDisjoint C := by
    rintro M₁ hM₁ M₂ hM₂ hne
    refine Set.disjoint_left.2 ?_
    rintro E ⟨hE, ⟨e₁⟩⟩ ⟨-, ⟨e₂⟩⟩
    obtain ⟨_, -, huniq⟩ := hRK (E.restrictScalars K) (hRU_sub E hE)
    exact hne ((huniq M₁ ⟨hM₁, ⟨e₁.symm⟩⟩).trans (huniq M₂ ⟨hM₂, ⟨e₂.symm⟩⟩).symm)
  have hRHS : (∑' E : R_U, w (E.1.restrictScalars K) / Nat.card (E.1 ≃ₐ[U] E.1)) =
      ∑' E : R_U, g E := rfl
  rw [hRHS, ← ENNReal.tsum_mul_left, hU_eq, tsum_biUnion hdisj]
  refine tsum_congr fun M ↦ ?_
  exact (tsum_fiber_div_natCard_algEquiv_eq (hRK_le M.1 M.2)
    (fun E ⟨e⟩ ↦ hRU E (hS_iso (hRK_sub M.2) e)) w hw).symm

/-- **Weighted class-sum relation over a normal intermediate field (divided form).** Divided form of
`TauCeti.mul_tsum_div_natCard_algEquiv_eq_of_le`:
`∑'_{M ∈ R_K} w(M) / #Aut_K(M) = (#Aut_K(U))⁻¹ · ∑'_{E ∈ R_U} w(E) / #Aut_U(E)`. -/
theorem tsum_div_natCard_algEquiv_eq_inv_mul_of_le {U : IntermediateField K Ω} [Normal K U]
    [Finite (U ≃ₐ[K] U)] {S R_K : Set (IntermediateField K Ω)}
    (hS_iso : ∀ {L M : IntermediateField K Ω}, L ∈ S → (L ≃ₐ[K] M) → M ∈ S)
    (hRK_le : ∀ M ∈ R_K, U ≤ M)
    (hRK_sub : R_K ⊆ S)
    (hRK : ∀ L ∈ S, ∃! M, M ∈ R_K ∧ Nonempty (L ≃ₐ[K] M))
    {R_U : Set (IntermediateField U Ω)}
    (hRU_sub : ∀ E ∈ R_U, E.restrictScalars K ∈ S)
    (hRU : ∀ E : IntermediateField U Ω, E.restrictScalars K ∈ S →
      ∃! F, F ∈ R_U ∧ Nonempty (E ≃ₐ[U] F))
    (w : IntermediateField K Ω → ℝ≥0∞)
    (hw : ∀ {L M : IntermediateField K Ω}, (L ≃ₐ[K] M) → w L = w M) :
    ∑' M : R_K, w M.1 / Nat.card (M.1 ≃ₐ[K] M.1) =
      (Nat.card (U ≃ₐ[K] U) : ℝ≥0∞)⁻¹ *
        ∑' E : R_U, w (E.1.restrictScalars K) / Nat.card (E.1 ≃ₐ[U] E.1) := by
  have hU_ne : (Nat.card (U ≃ₐ[K] U) : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.card_ne_zero.2 ⟨⟨1⟩, inferInstance⟩)
  rw [← mul_tsum_div_natCard_algEquiv_eq_of_le hS_iso hRK_le hRK_sub hRK hRU_sub hRU w hw,
    ← mul_assoc, ENNReal.inv_mul_cancel hU_ne (ENNReal.natCast_ne_top _), one_mul]

end NormalSubfieldSum

/-! ### Weighted isomorphism-class sums over the unramified base -/

section InertiaFamily

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **Weighted class-sum relation over the unramified base (multiplied form).** Let `S` be a set of
subextensions of `SeparableClosure K` closed under `K`-isomorphism whose members all have residue
degree `f ≠ 0`, and let `U = unramifiedExtension K (SeparableClosure K) f`. For any set `R_K` of
`K`-isomorphism representatives of `S`, any set `R_U` of `U`-isomorphism representatives of
`{E : IntermediateField U (SeparableClosure K) | E.restrictScalars K ∈ S}`, and any
`K`-isomorphism-invariant weight `w : IntermediateField K (SeparableClosure K) → ℝ≥0∞`,
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
    (hw : ∀ {L M : IntermediateField K (SeparableClosure K)}, (L ≃ₐ[K] M) → w L = w M) :
    (f : ℝ≥0∞) * ∑' M : R_K, w M.1 / Nat.card (M.1 ≃ₐ[K] M.1) =
      ∑' E : R_U, w (E.1.restrictScalars K) /
        Nat.card (E.1 ≃ₐ[unramifiedExtension K (SeparableClosure K) f] E.1) := by
  let U := unramifiedExtension K (SeparableClosure K) f
  have hUcard : Nat.card (U ≃ₐ[K] U) = f :=
    (IsGalois.card_aut_eq_finrank K U).trans (finrank_unramifiedExtension hf)
  have hRK_le : ∀ M ∈ R_K, U ≤ M := by
    intro M hM
    have hMdeg : M.inertiaDegree = f := hS_deg M (hRK_sub hM)
    have : Module.Finite K M := by
      by_contra h
      exact hf (hMdeg.symm.trans (M.inertiaDegree_eq_zero_iff.2 h))
    simpa [U, hMdeg] using M.unramifiedExtension_inertiaDegree_le
  have hmul := mul_tsum_div_natCard_algEquiv_eq_of_le hS_iso hRK_le hRK_sub hRK hRU_sub hRU w hw
  rwa [hUcard] at hmul

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
    (hw : ∀ {L M : IntermediateField K (SeparableClosure K)}, (L ≃ₐ[K] M) → w L = w M) :
    ∑' M : R_K, w M.1 / Nat.card (M.1 ≃ₐ[K] M.1) =
      (f : ℝ≥0∞)⁻¹ * ∑' E : R_U, w (E.1.restrictScalars K) /
        Nat.card (E.1 ≃ₐ[unramifiedExtension K (SeparableClosure K) f] E.1) := by
  rw [← mul_tsum_div_natCard_algEquiv_eq_of_inertiaDegree_eq hf hS_iso hS_deg hRK_sub hRK
      hRU_sub hRU w hw,
    ← mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast hf) (ENNReal.natCast_ne_top _),
    one_mul]

end InertiaFamily

/-! ### Specialization to totally ramified extensions over an unramified base -/

section FieldRangeBridge

variable {K F Ω : Type*} [Field K] [Field F] [Field Ω] [Algebra K F] [Algebra K Ω]
  [Algebra F Ω] [IsScalarTower K F Ω]

private theorem le_restrictScalars_of_fieldRange_eq {U : IntermediateField K Ω}
    (hU : (IsScalarTower.toAlgHom K F Ω).fieldRange = U) (E : IntermediateField F Ω) :
    U ≤ E.restrictScalars K := by
  rw [← hU]
  rintro _ ⟨x, rfl⟩
  exact E.algebraMap_mem x

/-- Given a scalar tower `K → F → Ω` of fields and `U = (IsScalarTower.toAlgHom K F Ω).fieldRange`,
intermediate fields of `Ω / F` correspond to intermediate fields of `Ω / U`. -/
private def intermediateFieldEquivOfFieldRangeEq {U : IntermediateField K Ω}
    (hU : (IsScalarTower.toAlgHom K F Ω).fieldRange = U) :
    IntermediateField F Ω ≃ IntermediateField U Ω :=
  have hmem (L : IntermediateField K Ω) :
      (∀ x : F, algebraMap F Ω x ∈ L) ↔ U ≤ L := by
    rw [← hU]
    exact ⟨by rintro h _ ⟨x, rfl⟩; exact h x, fun h x ↦ h ⟨x, rfl⟩⟩
  let ρ : IntermediateField F Ω ≃
      {L : IntermediateField K Ω // ∀ x : F, algebraMap F Ω x ∈ L} :=
    { toFun E := ⟨E.restrictScalars K, E.algebraMap_mem⟩
      invFun L := L.1.toSubfield.toIntermediateField L.2
      left_inv _ := rfl
      right_inv _ := rfl }
  ρ.trans ((Equiv.subtypeEquivRight hmem).trans (extendScalars.orderIso U).toEquiv)

private theorem intermediateFieldEquivOfFieldRangeEq_apply {U : IntermediateField K Ω}
    (hU : (IsScalarTower.toAlgHom K F Ω).fieldRange = U) (E : IntermediateField F Ω) :
    intermediateFieldEquivOfFieldRangeEq hU E =
      extendScalars (le_restrictScalars_of_fieldRange_eq hU E) := by
  simp [intermediateFieldEquivOfFieldRangeEq]

private theorem restrictScalars_intermediateFieldEquivOfFieldRangeEq {U : IntermediateField K Ω}
    (hU : (IsScalarTower.toAlgHom K F Ω).fieldRange = U) (E : IntermediateField F Ω) :
    (intermediateFieldEquivOfFieldRangeEq hU E).restrictScalars K = E.restrictScalars K := by
  rw [intermediateFieldEquivOfFieldRangeEq_apply, extendScalars_restrictScalars]

/-- Under `intermediateFieldEquivOfFieldRangeEq hU`, `F`-algebra equivalences `E₁ ≃ₐ[F] E₂`
correspond to `U`-algebra equivalences between the corresponding intermediate fields of `Ω / U`. -/
private def algEquivOfFieldRangeEq {U : IntermediateField K Ω}
    (hU : (IsScalarTower.toAlgHom K F Ω).fieldRange = U) (E₁ E₂ : IntermediateField F Ω) :
    (E₁ ≃ₐ[F] E₂) ≃
      (intermediateFieldEquivOfFieldRangeEq hU E₁ ≃ₐ[U]
        intermediateFieldEquivOfFieldRangeEq hU E₂) :=
  let h₁ := le_restrictScalars_of_fieldRange_eq hU E₁
  let h₂ := le_restrictScalars_of_fieldRange_eq hU E₂
  let ebase : (E₁ ≃ₐ[F] E₂) ≃
      {e : E₁.restrictScalars K ≃ₐ[K] E₂.restrictScalars K //
        ∀ y : U, (e ⟨y.1, h₁ y.2⟩ : Ω) = y.1} :=
    { toFun f := ⟨(restrictScalarsAlgEquiv K E₁).trans
          ((f.restrictScalars K).trans (restrictScalarsAlgEquiv K E₂).symm), fun y ↦ by
        have hyU : y.1 ∈ (IsScalarTower.toAlgHom K F Ω).fieldRange := hU.symm ▸ y.2
        obtain ⟨x, hx⟩ := hyU
        have hy : restrictScalarsAlgEquiv K E₁ ⟨y.1, h₁ y.2⟩ = algebraMap F E₁ x :=
          Subtype.ext (by simp [← hx])
        simp only [AlgEquiv.trans_apply, coe_restrictScalarsAlgEquiv_symm_apply, hy]
        exact (congrArg Subtype.val (f.commutes x)).trans (by simp [← hx])⟩
      invFun e := AlgEquiv.ofRingEquiv
        (f := ((restrictScalarsAlgEquiv K E₁).symm.trans
          (e.1.trans (restrictScalarsAlgEquiv K E₂))).toRingEquiv)
        fun x ↦ Subtype.ext <| by
          let y : U := ⟨algebraMap F Ω x, hU ▸ ⟨x, rfl⟩⟩
          have hx : (restrictScalarsAlgEquiv K E₁).symm (algebraMap F E₁ x) = ⟨y.1, h₁ y.2⟩ :=
            Subtype.ext (by simp [y])
          simp [AlgEquiv.trans_apply, hx, e.2 y, y]
      left_inv f := AlgEquiv.ext fun z ↦ Subtype.ext (by simp)
      right_inv e := Subtype.ext <| AlgEquiv.ext fun z ↦ Subtype.ext (by simp) }
  ebase.trans <| (extendScalarsAlgEquiv h₁ h₂).symm.trans <|
    (equivOfEq (intermediateFieldEquivOfFieldRangeEq_apply hU E₁).symm).equivCongr
      (equivOfEq (intermediateFieldEquivOfFieldRangeEq_apply hU E₂).symm)

end FieldRangeBridge

section TotallyRamifiedTransport

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra K F] [ValuativeExtension K F] [IsUnramified K F] [Algebra F (SeparableClosure K)]
  [IsScalarTower K F (SeparableClosure K)]

/-- The image of a finite unramified extension `F / K` inside `SeparableClosure K` is the canonical
unramified extension of degree `f(F / K)`. -/
private theorem fieldRange_toAlgHom_eq_unramifiedExtension :
    (IsScalarTower.toAlgHom K F (SeparableClosure K)).fieldRange =
      unramifiedExtension K (SeparableClosure K) (TauCeti.inertiaDegree K F) := by
  have : Module.Finite K F := finite_of_valuativeExtension K F
  let ι : F →ₐ[K] SeparableClosure K := IsScalarTower.toAlgHom K F (SeparableClosure K)
  have : Module.Finite K ι.fieldRange := Module.Finite.equiv ι.equivFieldRange.toLinearEquiv
  have hf : TauCeti.inertiaDegree K F ≠ 0 := TauCeti.inertiaDegree_pos.ne'
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_natCard_pow_inertiaDegree_sub_one K F
  have hζΩ : IsPrimitiveRoot (ι ζ) (Nat.card 𝓀[K] ^ TauCeti.inertiaDegree K F - 1) :=
    hζ.map_of_injective ι.injective
  have hrank : Module.finrank K ι.fieldRange =
      Module.finrank K
        (unramifiedExtension K (SeparableClosure K) (TauCeti.inertiaDegree K F)) := by
    rw [← ι.equivFieldRange.toLinearEquiv.finrank_eq,
      ← IsUnramified.inertiaDegree_eq_finrank (K := K) (L := F), finrank_unramifiedExtension hf]
  refine (eq_of_le_of_finrank_eq ?_ hrank.symm).symm
  rw [unramifiedExtension_eq_adjoin_simple hf hζΩ, adjoin_simple_le_iff]
  exact ⟨ζ, rfl⟩

/-- **Weighted isomorphism-class sum by residue degree ([Bhargava 2007, §2]).** Let `F` be an
unramified extension of `K` embedded in `SeparableClosure K` with residue degree `f = f(F / K)`.
For every set `R_K` of `K`-isomorphism representatives of the subextensions of degree `f * e` and
residue degree `f`, every set `R` of `F`-isomorphism representatives of `σ_F(e)`, every
`Φ : SeparableClosure F ≃ₐ[F] SeparableClosure K`, and every `K`-isomorphism-invariant weight `w`,
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
    (hw : ∀ {L M : IntermediateField K (SeparableClosure K)}, (L ≃ₐ[K] M) → w L = w M) :
    ∑' M : R_K, w M.1 / Nat.card (M.1 ≃ₐ[K] M.1) =
      (TauCeti.inertiaDegree K F : ℝ≥0∞)⁻¹ * ∑' E : R,
        w ((E.1.map Φ.toAlgHom).restrictScalars K) / Nat.card (E.1 ≃ₐ[F] E.1) := by
  have hf : TauCeti.inertiaDegree K F ≠ 0 := TauCeti.inertiaDegree_pos.ne'
  have hFrank : Module.finrank K F = TauCeti.inertiaDegree K F :=
    IsUnramified.inertiaDegree_eq_finrank.symm
  let U := unramifiedExtension K (SeparableClosure K) (TauCeti.inertiaDegree K F)
  have hU : (IsScalarTower.toAlgHom K F (SeparableClosure K)).fieldRange = U :=
    fieldRange_toAlgHom_eq_unramifiedExtension F
  let ψ := intermediateFieldEquivOfFieldRangeEq hU
  let θ : IntermediateField F (SeparableClosure F) ≃ IntermediateField U (SeparableClosure K) :=
    (orderIsoMapComap Φ).toEquiv.trans ψ
  let S : Set (IntermediateField K (SeparableClosure K)) :=
    {L | Module.finrank K L = TauCeti.inertiaDegree K F * e ∧
      L.inertiaDegree = TauCeti.inertiaDegree K F}
  have hS_iso : ∀ {L M : IntermediateField K (SeparableClosure K)}, L ∈ S → (L ≃ₐ[K] M) → M ∈ S :=
    fun ⟨hr, hi⟩ e₀ ↦ ⟨e₀.toLinearEquiv.finrank_eq.symm.trans hr,
      (IntermediateField.inertiaDegree_eq_of_algEquiv e₀).symm.trans hi⟩
  have hRU_sub : ∀ N ∈ θ '' R, N.restrictScalars K ∈ S := by
    rintro _ ⟨M, hM, rfl⟩
    have hmemR : (M.map Φ.toAlgHom).map Φ.symm.toAlgHom ∈ R := by
      rw [IntermediateField.map_map, Φ.symm_comp, IntermediateField.map_id]
      exact hM
    have hmem := (map_mem_totallyRamifiedOfDegree_iff F Φ (M.map Φ.toAlgHom) e).1
      (hR.subset hmemR)
    rw [hFrank] at hmem
    rwa [Equiv.trans_apply, restrictScalars_intermediateFieldEquivOfFieldRangeEq hU,
      OrderIso.coe_toEquiv, orderIsoMapComap_apply]
  have hRU : ∀ N : IntermediateField U (SeparableClosure K), N.restrictScalars K ∈ S →
      ∃! P, P ∈ θ '' R ∧ Nonempty (N ≃ₐ[U] P) := by
    intro N hN
    let E₀ : IntermediateField F (SeparableClosure K) := ψ.symm N
    have hN_eq : ψ E₀ = N := ψ.apply_symm_apply N
    have hE₀ : Module.finrank K (E₀.restrictScalars K) = Module.finrank K F * e ∧
        (E₀.restrictScalars K).inertiaDegree = TauCeti.inertiaDegree K F := by
      rw [← restrictScalars_intermediateFieldEquivOfFieldRangeEq hU E₀, hN_eq, hFrank]
      exact hN
    obtain ⟨M, ⟨hMR, hisoM⟩, huniq⟩ := hR.existsUnique
      ((map_mem_totallyRamifiedOfDegree_iff F Φ E₀ e).2 hE₀)
    have hbij (M' : IntermediateField F (SeparableClosure F)) :
        Nonempty (N ≃ₐ[U] θ M') ↔ Nonempty (E₀.map Φ.symm.toAlgHom ≃ₐ[F] M') := by
      rw [← hN_eq, Equiv.trans_apply, OrderIso.coe_toEquiv, orderIsoMapComap_apply]
      exact (((intermediateFieldMap Φ.symm E₀).symm.equivCongr (intermediateFieldMap Φ M')).trans
        (algEquivOfFieldRangeEq hU E₀ (M'.map Φ.toAlgHom))).symm.nonempty_congr
    refine ⟨θ M, ⟨⟨M, hMR, rfl⟩, (hbij M).2 hisoM⟩, ?_⟩
    rintro _ ⟨⟨M', hM'R, rfl⟩, hN'⟩
    exact congrArg θ (huniq M' ⟨hM'R, (hbij M').1 hN'⟩)
  rw [tsum_div_natCard_algEquiv_eq_inv_mul_of_inertiaDegree_eq hf hS_iso (fun _ hL ↦ hL.2)
      hRK_sub hRK hRU_sub hRU w hw]
  congr 1
  rw [← (Equiv.Set.image θ R θ.injective).tsum_eq]
  refine tsum_congr fun E ↦ ?_
  have hcard : Nat.card (θ E.1 ≃ₐ[U] θ E.1) = Nat.card (E.1 ≃ₐ[F] E.1) := by
    rw [Equiv.trans_apply, OrderIso.coe_toEquiv, orderIsoMapComap_apply]
    let α := intermediateFieldMap Φ E.1
    exact Nat.card_congr
      ((algEquivOfFieldRangeEq hU (E.1.map Φ.toAlgHom) (E.1.map Φ.toAlgHom)).symm.trans
        (α.symm.equivCongr α.symm))
  rw [Equiv.Set.image_apply, Subtype.coe_mk, hcard, Equiv.trans_apply,
    restrictScalars_intermediateFieldEquivOfFieldRangeEq hU, OrderIso.coe_toEquiv,
    orderIsoMapComap_apply]

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
    ∑' M : R_K, 1 / (Nat.card (M.1 ≃ₐ[K] M.1) : ℝ≥0∞) =
      (TauCeti.inertiaDegree K F : ℝ≥0∞)⁻¹ *
        ∑' E : R, 1 / (Nat.card (E.1 ≃ₐ[F] E.1) : ℝ≥0∞) := by
  have := isSepClosure_tower_top K F (SeparableClosure K)
  let Φ := IsSepClosure.equiv F (SeparableClosure F) (SeparableClosure K)
  exact tsum_div_natCard_algEquiv_eq_inv_mul_tsum_isRepresentativeSet F Φ hRK_sub hRK hR
    (fun _ ↦ 1) (fun _ ↦ rfl)

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
    ∑' M : R_K, 1 / ((Nat.card (M.1 ≃ₐ[K] M.1) : ℝ≥0∞) *
        (Nat.card 𝓀[K] : ℝ≥0∞) ^ M.1.discriminantExponent) =
      1 / ((TauCeti.inertiaDegree K F : ℝ≥0∞) *
        (Nat.card 𝓀[K] : ℝ≥0∞) ^ (TauCeti.inertiaDegree K F * (e - 1))) := by
  have := isSepClosure_tower_top K F (SeparableClosure K)
  let Φ := IsSepClosure.equiv F (SeparableClosure F) (SeparableClosure K)
  obtain ⟨R, hR⟩ := exists_isRepresentativeSet F e
  have hrel := tsum_div_natCard_algEquiv_eq_inv_mul_tsum_isRepresentativeSet F Φ hRK_sub hRK hR
    (fun L ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.discriminantExponent)
    (fun e₀ ↦ by rw [IntermediateField.discriminantExponent_eq_of_algEquiv e₀])
  have hLHS (M : R_K) :
      1 / ((Nat.card (M.1 ≃ₐ[K] M.1) : ℝ≥0∞) *
          (Nat.card 𝓀[K] : ℝ≥0∞) ^ M.1.discriminantExponent) =
        (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ M.1.discriminantExponent) /
          Nat.card (M.1 ≃ₐ[K] M.1) := by
    rw [one_div, one_div, div_eq_mul_inv,
      ENNReal.mul_inv (.inr (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))
        (.inl (ENNReal.natCast_ne_top _)), mul_comm]
  have hRHS (E : R) :
      (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ((E.1.map Φ.toAlgHom).restrictScalars K).discriminantExponent) /
          Nat.card (E.1 ≃ₐ[F] E.1) =
        1 / ((Nat.card (E.1 ≃ₐ[F] E.1) : ℝ≥0∞) * (Nat.card 𝓀[F] : ℝ≥0∞) ^ E.1.wildExponent) *
          (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (TauCeti.inertiaDegree K F * (e - 1))) := by
    have hmap : (E.1.map Φ.toAlgHom).map Φ.symm.toAlgHom = E.1 := by
      rw [IntermediateField.map_map, Φ.symm_comp, IntermediateField.map_id]
    have hmemR : (E.1.map Φ.toAlgHom).map Φ.symm.toAlgHom ∈ R := by
      rw [hmap]
      exact E.2
    have hdisc := one_div_natCard_residueField_pow_discriminantExponent_restrictScalars F Φ
      (E.1.map Φ.toAlgHom) (hR.subset hmemR)
    rw [hmap] at hdisc
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
    ∑' M : R_K, 1 / ((Nat.card (M.1 ≃ₐ[K] M.1) : ℝ≥0∞) *
        (Nat.card 𝓀[K] : ℝ≥0∞) ^ M.1.discriminantExponent) =
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
