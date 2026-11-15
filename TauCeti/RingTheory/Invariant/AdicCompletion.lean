/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import TauCeti.RingTheory.AdicCompletion.Localization
public import TauCeti.RingTheory.Ideal.Pointwise
public import TauCeti.RingTheory.Invariant.Basic

import Mathlib.RingTheory.AdicCompletion.Exactness
import TauCeti.RingTheory.AdicCompletion.CofinalLimit
import TauCeti.RingTheory.AdicCompletion.Coprime
import TauCeti.RingTheory.AdicCompletion.Extended
import TauCeti.RingTheory.AdicCompletion.LocalRing

/-!
# Adic completions of invariant rings and completed-local quotient comparison

Let a finite group `G` act on a commutative ring `S` by ring automorphisms over a Noetherian
invariant base ring `A` (`[Algebra.IsInvariant A S G]`) with `[Module.Finite A S]`, without any
invertibility assumption on `#G`. Exactness of `I`-adic completion on `0 → S^G → S → S^{#G}`
together with `AdicCompletion.mapAlgebraMapLinearEquiv` identifies the image of
`AdicCompletion I A →ₐ[A] AdicCompletion (I S) S` with the `G`-fixed subring even when `A → S` is
not injective.

At a maximal ideal `𝔪` of `S` lying over `𝔭` in `A`, the `G`-orbit of `𝔪` is a finite family of
pairwise coprime maximal ideals whose intersection has a power inside `𝔭 S`
(`Ideal.pow_card_mem_map_under`). Cofinal invariance, `AdicCompletion.coprimeEquiv`, and Shapiro's
lemma on the orbit identify the image of `AdicCompletion 𝔭 A →ₐ[A] AdicCompletion 𝔪 S` with the
`(MulAction.stabilizer G 𝔪)`-fixed subring (injective under `[FaithfulSMul A S]`). Consequently,
when `[FaithfulSMul A S]` and `[FaithfulSMul B S]`, for any subgroup `H ≥ MulAction.stabilizer G 𝔪`
and `H`-invariant intermediate ring `B` with `𝔪` lying over `𝔮` in `B`,
`AdicCompletion 𝔭 A ≃ₐ[A] AdicCompletion 𝔮 B`, completed stalks at `𝔭` and `𝔮` are isomorphic, and
local regularity transfers between any localizations `Aₚ` at `𝔭` and `B_𝔮` at `𝔮`.

## Main definitions and results

* `TauCeti.Algebra.IsInvariant.mem_range_mapₐ_ofId_iff`: the image of `AdicCompletion I A` in
  `AdicCompletion (I S) S` is the `G`-fixed subring.
* `TauCeti.Algebra.IsInvariant.mapₐ_ofId_injective_of_isMaximal` and
  `TauCeti.Algebra.IsInvariant.mem_range_mapₐ_ofId_iff_of_isMaximal`: injectivity (under
  `[FaithfulSMul A S]`) and decomposition-group fixed-point image at a maximal ideal `𝔪`.
* `TauCeti.Algebra.IsInvariant.mapₐ_ofId_bijective_of_stabilizer_le` and
  `TauCeti.Algebra.IsInvariant.adicCompletionEquivOfStabilizerLe`: `AdicCompletion 𝔭 A ≃ₐ[A]
  AdicCompletion 𝔮 B` when `MulAction.stabilizer G 𝔪 ≤ H`.
* `TauCeti.Algebra.IsInvariant.adicCompletionAtPrimeEquivOfStabilizerLe` (with
  `adicCompletionAtPrimeEquivOfStabilizerLe_mapₐ` and
  `adicCompletionAtPrimeEquivOfStabilizerLe_apply`) and
  `TauCeti.Algebra.IsInvariant.isRegularLocalRing_atPrime_iff_of_stabilizer_le`: completed-stalk
  isomorphism and local regularity comparison between localizations `Aₚ` and `B_𝔮`.

## References

* N. Bourbaki, *Commutative Algebra*, Chapter V, §2, no. 2, and *Lie Groups and Lie Algebras*,
  Chapter V, §5, Exercise 8.
* A. Grothendieck, *Revêtements étales et groupe fondamental (SGA 1)*, Exposé V, §2.
* L. Smith, *Polynomial Invariants of Finite Groups*, §7.5.
-/

public section

open Function
open scoped Pointwise

namespace TauCeti.Algebra.IsInvariant

section FixedSubalgebraSameUniverse

variable (A S G : Type*) [CommRing A] [CommRing S] [Algebra A S]
  [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G A S]

private noncomputable def defectMap :
    S →ₗ[FixedPoints.subalgebra A S G] Fin (Nat.card G) → S :=
  LinearMap.pi fun i ↦
    (MulSemiringAction.toAlgHom (FixedPoints.subalgebra A S G) S
      ((Finite.equivFin G).symm i)).toLinearMap - LinearMap.id

private theorem proj_comp_defectMap (i : Fin (Nat.card G)) :
    LinearMap.proj i ∘ₗ defectMap A S G =
      (MulSemiringAction.toAlgHom (FixedPoints.subalgebra A S G) S
        ((Finite.equivFin G).symm i)).toLinearMap - LinearMap.id :=
  LinearMap.ext fun _ ↦ rfl

private theorem exact_algebraLinearMap_defectMap :
    Function.Exact (Algebra.linearMap (FixedPoints.subalgebra A S G) S) (defectMap A S G) :=
  fun s ↦ ⟨fun hs ↦ ⟨⟨s, fun g ↦ by
    simpa [defectMap, sub_eq_zero] using congrFun hs (Finite.equivFin G g)⟩, rfl⟩,
    fun ⟨a, ha⟩ ↦ ha ▸ funext fun i ↦ by
      simpa [defectMap, sub_eq_zero] using a.2 ((Finite.equivFin G).symm i)⟩

private theorem mem_range_map_algebraLinearMap_subalgebra_iff
    [IsNoetherianRing (FixedPoints.subalgebra A S G)]
    [Module.Finite (FixedPoints.subalgebra A S G) S]
    (I₀ : Ideal (FixedPoints.subalgebra A S G)) (y : AdicCompletion I₀ S) :
    y ∈ Set.range (AdicCompletion.map I₀ (Algebra.linearMap (FixedPoints.subalgebra A S G) S)) ↔
      ∀ g : G, AdicCompletion.map I₀
        (MulSemiringAction.toAlgHom (FixedPoints.subalgebra A S G) S g).toLinearMap y = y := by
  have hexact := AdicCompletion.map_exact (I := I₀) (fun _ _ h ↦ Subtype.ext h)
    (fun s ↦ Subtype.ext_iff.trans (exact_algebraLinearMap_defectMap A S G s))
    (LinearMap.surjective_rangeRestrict (defectMap A S G))
  have hinj_sub := AdicCompletion.map_injective I₀
    (f := (LinearMap.range (defectMap A S G)).subtype) Subtype.val_injective
  have hsub : (LinearMap.range (defectMap A S G)).subtype ∘ₗ (defectMap A S G).rangeRestrict =
      defectMap A S G := LinearMap.ext fun _ ↦ rfl
  rw [← hexact y, ← hinj_sub.eq_iff, map_zero, AdicCompletion.map_comp_apply, hsub]
  refine ⟨fun hy g ↦ ?_, fun hy ↦ ?_⟩
  · have hi : AdicCompletion.map I₀
        (LinearMap.proj (Finite.equivFin G g) ∘ₗ defectMap A S G) y = 0 := by
      rw [← AdicCompletion.map_comp_apply, hy, map_zero]
    rwa [proj_comp_defectMap, Equiv.symm_apply_apply, map_sub, LinearMap.sub_apply,
      AdicCompletion.map_id, LinearMap.id_apply, sub_eq_zero] at hi
  · refine (AdicCompletion.piEquivOfFintype I₀ (fun _ : Fin (Nat.card G) ↦ S)).injective ?_
    rw [map_zero, AdicCompletion.piEquivOfFintype_apply]
    refine funext fun i ↦ ?_
    rw [Pi.zero_apply, AdicCompletion.pi, LinearMap.pi_apply, AdicCompletion.map_comp_apply,
      proj_comp_defectMap, map_sub, LinearMap.sub_apply, AdicCompletion.map_id,
      LinearMap.id_apply, sub_eq_zero]
    exact hy _

end FixedSubalgebraSameUniverse

section GlobalIdeal

variable {A S : Type*} (G : Type*) [CommRing A] [CommRing S] [Algebra A S]
  [Group G] [MulSemiringAction G S] [SMulCommClass G A S]

private theorem map_ofId_fixedPoints_map (I : Ideal A) :
    (I.map (algebraMap A (FixedPoints.subalgebra A S G))).map
      (algebraMap (FixedPoints.subalgebra A S G) S) = I.map (algebraMap A S) :=
  (I.map_map _ _).trans
    (congrArg I.map (IsScalarTower.algebraMap_eq A (FixedPoints.subalgebra A S G) S).symm)

variable (S) in
private noncomputable def extendedSubalgebraEquiv (I : Ideal A) :
    AdicCompletion (I.map (algebraMap A (FixedPoints.subalgebra A S G))) S
      ≃ₗ[FixedPoints.subalgebra A S G] AdicCompletion (I.map (algebraMap A S)) S :=
  (AdicCompletion.mapAlgebraMapLinearEquiv _ S S).trans
    ((AdicCompletion.equivOfPowLe
      ⟨1, (pow_one _).le.trans (map_ofId_fixedPoints_map (S := S) G I).le⟩
      ⟨1, (pow_one _).le.trans
        (map_ofId_fixedPoints_map (S := S) G I).ge⟩).toLinearEquiv.restrictScalars _)

private theorem extendedSubalgebraEquiv_apply (I : Ideal A)
    (y₀ : AdicCompletion (I.map (algebraMap A (FixedPoints.subalgebra A S G))) S) :
    extendedSubalgebraEquiv S G I y₀ =
      AdicCompletion.mapₐ (AlgHom.id A S)
        (fun _ hx ↦ Ideal.mem_comap.mpr ((map_ofId_fixedPoints_map (S := S) G I).le hx))
        (AdicCompletion.mapAlgebraMapLinearEquiv _ S S y₀) := by
  have heq := AdicCompletion.ofPowLe_eq_mapₐ_id (A := A)
    ⟨1, (pow_one _).le.trans (map_ofId_fixedPoints_map (S := S) G I).le⟩
    (fun _ hx ↦ Ideal.mem_comap.mpr ((map_ofId_fixedPoints_map (S := S) G I).le hx))
  rw [extendedSubalgebraEquiv, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    AlgEquiv.toLinearEquiv_apply, AdicCompletion.equivOfPowLe_apply,
    ← AlgHom.restrictScalars_apply A, heq]

private theorem extendedSubalgebraEquiv_map_algebraLinearMap (I : Ideal A)
    (hle : I ≤ (I.map (algebraMap A S)).comap (Algebra.ofId A S)) (x : AdicCompletion I A) :
    extendedSubalgebraEquiv S G I
      (AdicCompletion.map _ (Algebra.linearMap (FixedPoints.subalgebra A S G) S)
        (AdicCompletion.mapₐ (Algebra.ofId A (FixedPoints.subalgebra A S G))
          (fun _ hx ↦ Ideal.mem_comap.mpr
            (Ideal.mem_map_of_mem (algebraMap A (FixedPoints.subalgebra A S G)) hx)) x)) =
      AdicCompletion.mapₐ (Algebra.ofId A S) hle x := by
  let A₀ := FixedPoints.subalgebra A S G
  let I₀ : Ideal A₀ := I.map (algebraMap A A₀)
  have hAA₀ : I ≤ I₀.comap (Algebra.ofId A A₀) :=
    fun _ hx ↦ Ideal.mem_comap.mpr (Ideal.mem_map_of_mem (algebraMap A A₀) hx)
  have hA₀S : I₀ ≤ (I₀.map (algebraMap A₀ S)).comap ((Algebra.ofId A₀ S).restrictScalars A) :=
    fun _ hx ↦ Ideal.mem_comap.mpr (Ideal.mem_map_of_mem (algebraMap A₀ S) hx)
  rw [extendedSubalgebraEquiv_apply, AdicCompletion.mapAlgebraMapLinearEquiv_map_algebraLinearMap]
  have h₀ : AdicCompletion.mapₐ (Algebra.ofId A₀ S)
      (fun _ hx ↦ Ideal.mem_comap.mpr (Ideal.mem_map_of_mem (algebraMap A₀ S) hx))
      (AdicCompletion.mapₐ (Algebra.ofId A A₀) hAA₀ x) =
    AdicCompletion.mapₐ ((Algebra.ofId A₀ S).restrictScalars A) hA₀S
      (AdicCompletion.mapₐ (Algebra.ofId A A₀) hAA₀ x) := by
    apply AdicCompletion.mapₐ_congr; intro; rfl
  rw [h₀, AdicCompletion.mapₐ_mapₐ, AdicCompletion.mapₐ_mapₐ]
  exact AdicCompletion.mapₐ_congr (fun a ↦ (IsScalarTower.algebraMap_apply A A₀ S a).symm) x

private theorem extendedSubalgebraEquiv_map_toAlgHom (I : Ideal A)
    (hg_le : ∀ g : G,
      I.map (algebraMap A S) ≤ (I.map (algebraMap A S)).comap (MulSemiringAction.toAlgHom A S g))
    (g : G) (y₀ : AdicCompletion (I.map (algebraMap A (FixedPoints.subalgebra A S G))) S) :
    extendedSubalgebraEquiv S G I
      (AdicCompletion.map _
        (MulSemiringAction.toAlgHom (FixedPoints.subalgebra A S G) S g).toLinearMap y₀) =
      AdicCompletion.mapₐ (MulSemiringAction.toAlgHom A S g) (hg_le g)
        (extendedSubalgebraEquiv S G I y₀) := by
  let A₀ := FixedPoints.subalgebra A S G
  let I₀ : Ideal A₀ := I.map (algebraMap A A₀)
  let z := AdicCompletion.mapAlgebraMapLinearEquiv I₀ S S y₀
  have hg₀ : I₀.map (algebraMap A₀ S) ≤
      (I₀.map (algebraMap A₀ S)).comap (MulSemiringAction.toAlgHom A₀ S g) :=
    Ideal.map_le_iff_le_comap.mpr fun r hr ↦ Ideal.mem_comap.mpr <| Ideal.mem_comap.mpr
      (((MulSemiringAction.toAlgHom A₀ S g).commutes r).symm ▸
        Ideal.mem_map_of_mem (algebraMap A₀ S) hr)
  have hg₀A : I₀.map (algebraMap A₀ S) ≤
      (I₀.map (algebraMap A₀ S)).comap ((MulSemiringAction.toAlgHom A₀ S g).restrictScalars A) :=
    hg₀
  rw [extendedSubalgebraEquiv_apply, extendedSubalgebraEquiv_apply,
    AdicCompletion.mapAlgebraMapLinearEquiv_map_algHom I₀ (MulSemiringAction.toAlgHom A₀ S g) hg₀]
  have h₀ : AdicCompletion.mapₐ (MulSemiringAction.toAlgHom A₀ S g) hg₀ z =
      AdicCompletion.mapₐ ((MulSemiringAction.toAlgHom A₀ S g).restrictScalars A) hg₀A z := by
    apply AdicCompletion.mapₐ_congr; intro; rfl
  rw [h₀, AdicCompletion.mapₐ_mapₐ, AdicCompletion.mapₐ_mapₐ]
  apply AdicCompletion.mapₐ_congr; intro; rfl

variable {G} [Finite G] [IsNoetherianRing A] [Module.Finite A S] in
/-- **Invariants of an adic completion along an extended ideal.** For a finite group `G` acting on
`S` with Noetherian invariant base ring `A` (`[Algebra.IsInvariant A S G]`, not necessarily
injective into `S`) and `S` module-finite over `A`, the image of `AdicCompletion I A` inside
`AdicCompletion (I.map (algebraMap A S)) S` consists precisely of the `G`-fixed elements. -/
theorem mem_range_mapₐ_ofId_iff [Algebra.IsInvariant A S G] (I : Ideal A)
    (hle : I ≤ (I.map (algebraMap A S)).comap (Algebra.ofId A S) :=
      fun _ hx ↦ Ideal.mem_comap.mpr (Ideal.mem_map_of_mem _ hx))
    (hg_le : ∀ g : G, I.map (algebraMap A S) ≤
      (I.map (algebraMap A S)).comap (MulSemiringAction.toAlgHom A S g) := I.map_le_comap_toAlgHom)
    (y : AdicCompletion (I.map (algebraMap A S)) S) :
    y ∈ Set.range (AdicCompletion.mapₐ (Algebra.ofId A S) hle) ↔
      ∀ g : G, AdicCompletion.mapₐ (MulSemiringAction.toAlgHom A S g) (hg_le g) y = y := by
  let A₀ := FixedPoints.subalgebra A S G
  have hπ : Function.Surjective (Algebra.ofId A A₀) := fun d ↦
    let ⟨a, ha⟩ := Algebra.IsInvariant.isInvariant (A := A) (G := G) d.1 d.2; ⟨a, Subtype.ext ha⟩
  have : IsNoetherianRing A₀ := isNoetherianRing_of_surjective A A₀ (Algebra.ofId A A₀).toRingHom hπ
  have : Module.Finite A₀ S := Module.Finite.of_restrictScalars_finite A A₀ S
  refine ⟨fun ⟨x, hx⟩ g ↦ hx ▸ ?_, fun hfix ↦ ?_⟩
  · rw [AdicCompletion.mapₐ_mapₐ]
    exact AdicCompletion.mapₐ_congr ((MulSemiringAction.toAlgHom A S g).commutes) x
  · set y₀ := (extendedSubalgebraEquiv S G I).symm y
    have hy : extendedSubalgebraEquiv S G I y₀ = y := LinearEquiv.apply_symm_apply _ y
    obtain ⟨x₀, hx₀⟩ := (mem_range_map_algebraLinearMap_subalgebra_iff _ _ _ _ _).mpr fun g ↦
      (extendedSubalgebraEquiv S G I).injective <| by
        rw [extendedSubalgebraEquiv_map_toAlgHom G I hg_le g y₀, hy]; exact hfix g
    obtain ⟨x', hx'⟩ := (AdicCompletion.mapAlgebraMapLinearEquiv I A₀ A₀).surjective x₀
    obtain ⟨x, rfl⟩ := AdicCompletion.map_surjective I (f := Algebra.linearMap A A₀) hπ x'
    refine ⟨x, ?_⟩
    rw [← extendedSubalgebraEquiv_map_algebraLinearMap G I hle x,
      (AdicCompletion.mapAlgebraMapLinearEquiv_map_algebraLinearMap I x).symm.trans hx', hx₀, hy]

end GlobalIdeal

section MaximalIdeal

variable {A S : Type*} (G : Type*) [CommRing A] [CommRing S] [Algebra A S]
  [Group G] [MulSemiringAction G S] [SMulCommClass G A S] (𝔭 : Ideal A) (𝔪 : Ideal S)

private theorem pairwise_isCoprime_orbit [𝔪.IsMaximal] :
    Pairwise (IsCoprime on fun Q : MulAction.orbit G 𝔪 ↦ Q.1) := fun Q₁ Q₂ hne ↦ by
  obtain ⟨g₁, hg₁⟩ := MulAction.mem_orbit_iff.mp Q₁.2
  obtain ⟨g₂, hg₂⟩ := MulAction.mem_orbit_iff.mp Q₂.2
  have : Q₁.1.IsMaximal := hg₁ ▸ inferInstance
  have : Q₂.1.IsMaximal := hg₂ ▸ inferInstance
  exact Ideal.isCoprime_of_isMaximal (Subtype.coe_ne_coe.mpr hne)

private def orbitInf : Ideal S := ⨅ Q : MulAction.orbit G 𝔪, Q.1

private theorem inv_smul_mem_orbit (g : G) (Q : MulAction.orbit G 𝔪) :
    g⁻¹ • Q.1 ∈ MulAction.orbit G 𝔪 :=
  let ⟨h, hh⟩ := MulAction.mem_orbit_iff.mp Q.2
  MulAction.mem_orbit_iff.mpr ⟨g⁻¹ * h, by rw [mul_smul, hh]⟩

private theorem orbitInf_stable (g : G) {s : S} (hs : s ∈ orbitInf G 𝔪) :
    g • s ∈ orbitInf G 𝔪 :=
  Ideal.mem_iInf.mpr fun Q ↦ Ideal.mem_inv_pointwise_smul_iff.mp
    ((Ideal.mem_iInf.mp hs) ⟨g⁻¹ • Q.1, inv_smul_mem_orbit G 𝔪 g Q⟩)

private theorem under_orbitInf [𝔪.LiesOver 𝔭] : (orbitInf G 𝔪).under A = 𝔭 := by
  ext a
  simp only [Ideal.mem_under, orbitInf, Ideal.mem_iInf]
  refine ⟨fun ha ↦ ?_, fun ha Q ↦ ?_⟩
  · have h₀ := ha ⟨𝔪, MulAction.mem_orbit_self 𝔪⟩
    rwa [← Ideal.mem_under, ← ‹𝔪.LiesOver 𝔭›.over] at h₀
  · obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp Q.2
    have hQ : Q.1.under A = 𝔭 := by rw [← hg, Ideal.under_smul, ‹𝔪.LiesOver 𝔭›.over]
    rwa [← hQ, Ideal.mem_under] at ha

private theorem map_le_orbitInf [𝔪.LiesOver 𝔭] : 𝔭.map (algebraMap A S) ≤ orbitInf G 𝔪 :=
  Ideal.map_le_iff_le_comap.mpr (under_orbitInf G 𝔭 𝔪).ge

private noncomputable def orbitPiMapₐ [𝔪.LiesOver 𝔭] :
    AdicCompletion (𝔭.map (algebraMap A S)) S →ₐ[A]
      ∀ Q : MulAction.orbit G 𝔪, AdicCompletion Q.1 S :=
  (AlgHom.pi fun Q : MulAction.orbit G 𝔪 ↦
      AdicCompletion.mapₐ (AlgHom.id A S)
        (fun _ hx ↦ Ideal.mem_comap.mpr (iInf_le (fun R : MulAction.orbit G 𝔪 ↦ R.1) Q hx))).comp
    (AdicCompletion.mapₐ (AlgHom.id A S)
      (fun _ hx ↦ Ideal.mem_comap.mpr (map_le_orbitInf G 𝔭 𝔪 hx)))

private theorem orbitPiMapₐ_eq_mapₐ [𝔪.LiesOver 𝔭]
    (y : AdicCompletion (𝔭.map (algebraMap A S)) S) (Q : MulAction.orbit G 𝔪) :
    orbitPiMapₐ G 𝔭 𝔪 y Q =
      AdicCompletion.mapₐ (AlgHom.id A S)
        (fun _ hx ↦ Ideal.mem_comap.mpr
          (((map_le_orbitInf G 𝔭 𝔪).trans (iInf_le (fun R : MulAction.orbit G 𝔪 ↦ R.1) Q)) hx))
        y := by
  simp only [orbitPiMapₐ, AlgHom.comp_apply, AlgHom.pi_apply, AdicCompletion.mapₐ_mapₐ]
  apply AdicCompletion.mapₐ_congr; intro; rfl

variable [Finite G] [FaithfulSMul A S] [IsNoetherianRing A] [Module.Finite A S]
  [𝔪.IsMaximal] [𝔪.LiesOver 𝔭]

omit [FaithfulSMul A S] [𝔪.IsMaximal] in
private theorem exists_orbitInf_pow_le_map [Algebra.IsInvariant A S G] :
    ∃ k : ℕ, orbitInf G 𝔪 ^ k ≤ 𝔭.map (algebraMap A S) :=
  Ideal.exists_pow_le_of_le_radical_of_fg
    (fun _ hb ↦ ⟨Nat.card G, under_orbitInf G 𝔭 𝔪 ▸
      Ideal.pow_card_mem_map_under A G (orbitInf_stable G 𝔪) hb⟩)
    ((IsNoetherianRing.of_finite A S).noetherian (orbitInf G 𝔪))

omit [FaithfulSMul A S] in
private theorem orbitPiMapₐ_bijective [Algebra.IsInvariant A S G] :
    Function.Bijective (orbitPiMapₐ G 𝔭 𝔪) := by
  have : Finite (MulAction.orbit G 𝔪) := (Set.finite_range _).to_subtype
  exact (AdicCompletion.pi_mapₐ_id_bijective_of_pairwise_isCoprime
    (fun Q : MulAction.orbit G 𝔪 ↦ Q.1) (pairwise_isCoprime_orbit G 𝔪)).comp
    (AdicCompletion.mapₐ_id_bijective_of_pow_le
      (fun _ hx ↦ Ideal.mem_comap.mpr (map_le_orbitInf G 𝔭 𝔪 hx))
      (exists_orbitInf_pow_le_map G 𝔭 𝔪))

/-- **Completed invariant ring injects into completion at a maximal ideal.** For a finite group `G`
acting on `S` with Noetherian faithful invariant base ring `A` and `S` module-finite over `A`, if
`𝔪` is a maximal ideal of `S` lying over `𝔭` in `A`, then
`AdicCompletion 𝔭 A →ₐ[A] AdicCompletion 𝔪 S` is injective. -/
theorem mapₐ_ofId_injective_of_isMaximal [Algebra.IsInvariant A S G]
    (h𝔭𝔪 : 𝔭 ≤ 𝔪.comap (Algebra.ofId A S) :=
      fun a ha ↦ Ideal.mem_comap.mpr ((𝔪.mem_of_liesOver 𝔭 a).mp ha)) :
    Function.Injective (AdicCompletion.mapₐ (Algebra.ofId A S) h𝔭𝔪) := by
  have hle : 𝔭 ≤ (𝔭.map (algebraMap A S)).comap (Algebra.ofId A S) :=
    fun _ hx ↦ Ideal.mem_comap.mpr (Ideal.mem_map_of_mem _ hx)
  intro x₁ x₂ hx
  refine AdicCompletion.mapₐ_ofId_injective 𝔭 hle <| (orbitPiMapₐ_bijective G 𝔭 𝔪).injective ?_
  funext Q
  obtain ⟨g, hgQ⟩ := MulAction.mem_orbit_iff.mp Q.2
  have hcoord (x : AdicCompletion 𝔭 A) :
      orbitPiMapₐ G 𝔭 𝔪 (AdicCompletion.mapₐ (Algebra.ofId A S) hle x) Q =
        AdicCompletion.mapₐ (MulSemiringAction.toAlgHom A S g)
          (fun s hs ↦ Ideal.mem_comap.mpr (hgQ ▸ Ideal.smul_mem_pointwise_smul g s 𝔪 hs))
          (AdicCompletion.mapₐ (Algebra.ofId A S) h𝔭𝔪 x) := by
    rw [orbitPiMapₐ_eq_mapₐ, AdicCompletion.mapₐ_mapₐ, AdicCompletion.mapₐ_mapₐ]
    exact AdicCompletion.mapₐ_congr (fun a ↦ ((MulSemiringAction.toAlgHom A S g).commutes a).symm) x
  rw [hcoord x₁, hcoord x₂, hx]

omit [Finite G] [FaithfulSMul A S] [IsNoetherianRing A] [Module.Finite A S] [𝔪.IsMaximal] in
private theorem orbitPiMapₐ_mapₐ_toAlgHom (g : G)
    (y : AdicCompletion (𝔭.map (algebraMap A S)) S) (Q : MulAction.orbit G 𝔪) :
    orbitPiMapₐ G 𝔭 𝔪
      (AdicCompletion.mapₐ (MulSemiringAction.toAlgHom A S g) (𝔭.map_le_comap_toAlgHom g) y) Q =
      AdicCompletion.mapₐ (MulSemiringAction.toAlgHom A S g)
        (fun _ hs ↦ Ideal.mem_comap.mpr (Ideal.mem_inv_pointwise_smul_iff.mp hs))
        (orbitPiMapₐ G 𝔭 𝔪 y ⟨g⁻¹ • Q.1, inv_smul_mem_orbit G 𝔪 g Q⟩) := by
  rw [orbitPiMapₐ_eq_mapₐ, orbitPiMapₐ_eq_mapₐ, AdicCompletion.mapₐ_mapₐ, AdicCompletion.mapₐ_mapₐ]
  apply AdicCompletion.mapₐ_congr; intro; rfl

variable {G} in
omit [FaithfulSMul A S] in
/-- **Decomposition-group invariants of the completion at a maximal ideal.** For a finite group `G`
acting on `S` with Noetherian invariant base ring `A` and `S` module-finite over `A`, if `𝔪` is a
maximal ideal of `S` lying over `𝔭` in `A`, then the image of `AdicCompletion 𝔭 A` inside
`AdicCompletion 𝔪 S` consists precisely of the `(MulAction.stabilizer G 𝔪)`-fixed elements. -/
theorem mem_range_mapₐ_ofId_iff_of_isMaximal [Algebra.IsInvariant A S G]
    (h𝔭𝔪 : 𝔭 ≤ 𝔪.comap (Algebra.ofId A S) :=
      fun a ha ↦ Ideal.mem_comap.mpr ((𝔪.mem_of_liesOver 𝔭 a).mp ha))
    (z : AdicCompletion 𝔪 S) :
    z ∈ Set.range (AdicCompletion.mapₐ (Algebra.ofId A S) h𝔭𝔪) ↔
      ∀ g (hg : g ∈ MulAction.stabilizer G 𝔪),
        AdicCompletion.mapₐ (MulSemiringAction.toAlgHom A S g)
          (𝔪.le_comap_toAlgHom_of_mem_stabilizer hg) z = z := by
  refine ⟨fun ⟨x, hx⟩ g hg ↦ hx ▸ ?_, fun hz ↦ ?_⟩
  · rw [AdicCompletion.mapₐ_mapₐ]
    exact AdicCompletion.mapₐ_congr ((MulSemiringAction.toAlgHom A S g).commutes) x
  · have hle : 𝔭 ≤ (𝔭.map (algebraMap A S)).comap (Algebra.ofId A S) :=
      fun _ hx ↦ Ideal.mem_comap.mpr (Ideal.mem_map_of_mem _ hx)
    choose γ hγ using fun Q : MulAction.orbit G 𝔪 ↦ MulAction.mem_orbit_iff.mp Q.2
    let f : ∀ Q : MulAction.orbit G 𝔪, AdicCompletion Q.1 S := fun Q ↦
      AdicCompletion.mapₐ (MulSemiringAction.toAlgHom A S (γ Q))
        (fun s hs ↦ Ideal.mem_comap.mpr (hγ Q ▸ Ideal.smul_mem_pointwise_smul (γ Q) s 𝔪 hs)) z
    obtain ⟨y, hy⟩ := (orbitPiMapₐ_bijective G 𝔭 𝔪).surjective f
    obtain ⟨x, rfl⟩ : y ∈ Set.range (AdicCompletion.mapₐ (Algebra.ofId A S) hle) := by
      refine (mem_range_mapₐ_ofId_iff (G := G) 𝔭 hle 𝔭.map_le_comap_toAlgHom y).mpr
        fun g ↦ (orbitPiMapₐ_bijective G 𝔭 𝔪).injective <| funext fun Q ↦ ?_
      let Q' : MulAction.orbit G 𝔪 := ⟨g⁻¹ • Q.1, inv_smul_mem_orbit G 𝔪 g Q⟩
      rw [orbitPiMapₐ_mapₐ_toAlgHom G 𝔭 𝔪 g y Q, hy]; dsimp only [f]
      have hk_mem : (γ Q)⁻¹ * (g * γ Q') ∈ MulAction.stabilizer G 𝔪 := by
        rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hγ Q', smul_inv_smul,
          ← hγ Q, inv_smul_smul]
      conv_rhs => rw [← hz _ hk_mem]
      rw [AdicCompletion.mapₐ_mapₐ, AdicCompletion.mapₐ_mapₐ]
      exact AdicCompletion.mapₐ_congr (fun s ↦ by simp [mul_smul, Q']) z
    let Q₀ : MulAction.orbit G 𝔪 := ⟨𝔪, MulAction.mem_orbit_self 𝔪⟩
    have hf₀ : f Q₀ = z := hz (γ Q₀) (MulAction.mem_stabilizer_iff.mpr (hγ Q₀))
    refine ⟨x, (?_ : AdicCompletion.mapₐ (Algebra.ofId A S) h𝔭𝔪 x =
      orbitPiMapₐ G 𝔭 𝔪 (AdicCompletion.mapₐ (Algebra.ofId A S) hle x) Q₀).trans
      ((congrFun hy Q₀).trans hf₀)⟩
    rw [orbitPiMapₐ_eq_mapₐ, AdicCompletion.mapₐ_mapₐ]
    apply AdicCompletion.mapₐ_congr; intro; rfl

end MaximalIdeal

section QuotientComparison

private theorem mapₐ_toAlgHom_subgroup_eq {S G : Type*} [CommRing S] [Group G]
    [MulSemiringAction G S] (𝔪 : Ideal S) (A B : Type*) [CommRing A] [CommRing B]
    [Algebra A S] [Algebra B S] [SMulCommClass G A S] (H : Subgroup G) [SMulCommClass H B S]
    {g : G} (hg : g ∈ MulAction.stabilizer G 𝔪) (h : H) (hhG : (h : G) = g)
    (hh : h ∈ MulAction.stabilizer H 𝔪) (z : AdicCompletion 𝔪 S) :
    AdicCompletion.mapₐ (MulSemiringAction.toAlgHom A S g)
        (𝔪.le_comap_toAlgHom_of_mem_stabilizer hg) z =
      AdicCompletion.mapₐ (MulSemiringAction.toAlgHom B S h)
        (𝔪.le_comap_toAlgHom_of_mem_stabilizer hh) z :=
  AdicCompletion.mapₐ_congr (fun s ↦ by simp [← hhG, Subgroup.smul_def]) z

variable {A B S G : Type*} [CommRing A] [CommRing B] [CommRing S]
  [Algebra A B] [Algebra B S] [Algebra A S] [IsScalarTower A B S]
  [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G A S]
  [Algebra.IsInvariant A S G] [FaithfulSMul A S] [IsNoetherianRing A] [Module.Finite A S]
  (H : Subgroup G) [SMulCommClass H B S] [Algebra.IsInvariant B S H] [FaithfulSMul B S]
  (𝔭 : Ideal A) (𝔮 : Ideal B) (𝔪 : Ideal S) [𝔪.IsMaximal] [𝔪.LiesOver 𝔭] [𝔪.LiesOver 𝔮]

/-- **Completed-local quotient comparison.** If `H ≤ G` contains `MulAction.stabilizer G 𝔪` for a
maximal ideal `𝔪` of `S`, and `B` is an `H`-invariant intermediate ring between `A` and `S` with `𝔪`
lying over `𝔮` in `B` and `𝔭` in `A`, then `AdicCompletion 𝔭 A →ₐ[A] AdicCompletion 𝔮 B` is
bijective. -/
theorem mapₐ_ofId_bijective_of_stabilizer_le (hH : MulAction.stabilizer G 𝔪 ≤ H)
    (h𝔭𝔮 : 𝔭 ≤ 𝔮.comap (Algebra.ofId A B) :=
      (have := Ideal.LiesOver.tower_bot 𝔪 𝔮 𝔭;
        fun a ha ↦ Ideal.mem_comap.mpr ((𝔮.mem_of_liesOver 𝔭 a).mp ha))) :
    Function.Bijective (AdicCompletion.mapₐ (Algebra.ofId A B) h𝔭𝔮) := by
  have : IsNoetherian A S := isNoetherian_of_isNoetherianRing_of_finite A S
  have : IsNoetherianRing B := isNoetherian_of_tower A
    (isNoetherian_of_injective (IsScalarTower.toAlgHom A B S).toLinearMap
      (FaithfulSMul.algebraMap_injective B S))
  have : Module.Finite B S := Module.Finite.of_restrictScalars_finite A B S
  have h𝔮𝔪 : 𝔮 ≤ 𝔪.comap (Algebra.ofId B S) :=
    fun b hb ↦ Ideal.mem_comap.mpr ((𝔪.mem_of_liesOver 𝔮 b).mp hb)
  have h𝔭𝔪 : 𝔭 ≤ 𝔪.comap (Algebra.ofId A S) :=
    fun a ha ↦ Ideal.mem_comap.mpr ((𝔪.mem_of_liesOver 𝔭 a).mp ha)
  have hcomp (x : AdicCompletion 𝔭 A) :
      AdicCompletion.mapₐ (Algebra.ofId B S) h𝔮𝔪 (AdicCompletion.mapₐ (Algebra.ofId A B) h𝔭𝔮 x) =
        AdicCompletion.mapₐ (Algebra.ofId A S) h𝔭𝔪 x := by
    have hrestrict :
        AdicCompletion.mapₐ (Algebra.ofId B S) h𝔮𝔪 (AdicCompletion.mapₐ (Algebra.ofId A B) h𝔭𝔮 x) =
          AdicCompletion.mapₐ ((Algebra.ofId B S).restrictScalars A)
            (fun b hb ↦ Ideal.mem_comap.mpr ((𝔪.mem_of_liesOver 𝔮 b).mp hb))
            (AdicCompletion.mapₐ (Algebra.ofId A B) h𝔭𝔮 x) := by
      apply AdicCompletion.mapₐ_congr; intro; rfl
    rw [hrestrict, AdicCompletion.mapₐ_mapₐ]
    exact AdicCompletion.mapₐ_congr (fun a ↦ (IsScalarTower.algebraMap_apply A B S a).symm) x
  refine ⟨fun x₁ x₂ hx ↦ mapₐ_ofId_injective_of_isMaximal G 𝔭 𝔪 h𝔭𝔪 ?_, fun y ↦ ?_⟩
  · rw [← hcomp x₁, ← hcomp x₂, hx]
  · set z : AdicCompletion 𝔪 S := AdicCompletion.mapₐ (Algebra.ofId B S) h𝔮𝔪 y
    have hzH := (mem_range_mapₐ_ofId_iff_of_isMaximal (G := H) 𝔮 𝔪 h𝔮𝔪 z).mp ⟨y, rfl⟩
    obtain ⟨x, hx⟩ : z ∈ Set.range (AdicCompletion.mapₐ (Algebra.ofId A S) h𝔭𝔪) := by
      refine (mem_range_mapₐ_ofId_iff_of_isMaximal (G := G) 𝔭 𝔪 h𝔭𝔪 z).mpr fun g hg ↦ ?_
      let h : H := ⟨g, hH hg⟩
      have hh : h ∈ MulAction.stabilizer H 𝔪 :=
        MulAction.mem_stabilizer_iff.mpr (MulAction.mem_stabilizer_iff.mp hg)
      exact (mapₐ_toAlgHom_subgroup_eq 𝔪 A B H hg h rfl hh z).trans (hzH h hh)
    exact ⟨x, mapₐ_ofId_injective_of_isMaximal H 𝔮 𝔪 h𝔮𝔪 ((hcomp x).trans hx)⟩

/-- Bundled `A`-algebra isomorphism `AdicCompletion 𝔭 A ≃ₐ[A] AdicCompletion 𝔮 B` when
`MulAction.stabilizer G 𝔪 ≤ H`. -/
noncomputable def adicCompletionEquivOfStabilizerLe (hH : MulAction.stabilizer G 𝔪 ≤ H) :
    AdicCompletion 𝔭 A ≃ₐ[A] AdicCompletion 𝔮 B :=
  AlgEquiv.ofBijective
    (AdicCompletion.mapₐ (Algebra.ofId A B)
      (have := Ideal.LiesOver.tower_bot 𝔪 𝔮 𝔭;
        fun a ha ↦ Ideal.mem_comap.mpr ((𝔮.mem_of_liesOver 𝔭 a).mp ha)))
    (mapₐ_ofId_bijective_of_stabilizer_le H 𝔭 𝔮 𝔪 hH)

/-- Applying `adicCompletionEquivOfStabilizerLe` agrees with
`AdicCompletion.mapₐ (Algebra.ofId A B)`. -/
@[simp] theorem adicCompletionEquivOfStabilizerLe_apply (hH : MulAction.stabilizer G 𝔪 ≤ H)
    (x : AdicCompletion 𝔭 A) :
    adicCompletionEquivOfStabilizerLe H 𝔭 𝔮 𝔪 hH x =
      AdicCompletion.mapₐ (Algebra.ofId A B)
        (have := Ideal.LiesOver.tower_bot 𝔪 𝔮 𝔭;
          fun a ha ↦ Ideal.mem_comap.mpr ((𝔮.mem_of_liesOver 𝔭 a).mp ha)) x := by
  rw [adicCompletionEquivOfStabilizerLe, AlgEquiv.ofBijective_apply]

/-- `adicCompletionEquivOfStabilizerLe` extends `algebraMap A B` along `AdicCompletion.of`. -/
theorem adicCompletionEquivOfStabilizerLe_of (hH : MulAction.stabilizer G 𝔪 ≤ H) (a : A) :
    adicCompletionEquivOfStabilizerLe H 𝔭 𝔮 𝔪 hH (AdicCompletion.of 𝔭 A a) =
      AdicCompletion.of 𝔮 B (algebraMap A B a) := by simp

/-- **Completed-stalk quotient comparison.** Under the hypotheses of
`mapₐ_ofId_bijective_of_stabilizer_le`, for any localizations `Aₚ` of `A` at `𝔭` and `B_𝔮` of `B` at
`𝔮`, their completions along their maximal ideals are canonically isomorphic as `A`-algebras. -/
noncomputable def adicCompletionAtPrimeEquivOfStabilizerLe (hH : MulAction.stabilizer G 𝔪 ≤ H)
    (Aₚ : Type*) [CommRing Aₚ] [Algebra A Aₚ] [𝔭.IsPrime] [IsLocalization.AtPrime Aₚ 𝔭]
    [IsLocalRing Aₚ] (B_𝔮 : Type*) [CommRing B_𝔮] [Algebra B B_𝔮] [Algebra A B_𝔮]
    [IsScalarTower A B B_𝔮] [𝔮.IsPrime] [IsLocalization.AtPrime B_𝔮 𝔮] [IsLocalRing B_𝔮] :
    AdicCompletion (IsLocalRing.maximalIdeal Aₚ) Aₚ ≃ₐ[A]
      AdicCompletion (IsLocalRing.maximalIdeal B_𝔮) B_𝔮 :=
  have := Algebra.IsInvariant.isIntegral A S G; have := Algebra.IsInvariant.isIntegral B S H
  have : 𝔭.IsMaximal := ‹𝔪.LiesOver 𝔭›.over ▸ Ideal.isMaximal_under_of_isIntegral_of_isMaximal 𝔪
  have : 𝔮.IsMaximal := ‹𝔪.LiesOver 𝔮›.over ▸ Ideal.isMaximal_under_of_isIntegral_of_isMaximal 𝔪
  (AdicCompletion.equivMaximalIdealOfAtPrime 𝔭 Aₚ).symm.trans
    ((adicCompletionEquivOfStabilizerLe H 𝔭 𝔮 𝔪 hH).trans
      ((AdicCompletion.equivMaximalIdealOfAtPrime 𝔮 B_𝔮).restrictScalars A))

/-- `adicCompletionAtPrimeEquivOfStabilizerLe` intertwines the canonical completion maps out of
`AdicCompletion 𝔭 A` and `AdicCompletion 𝔮 B` via `adicCompletionEquivOfStabilizerLe`. -/
@[simp] theorem adicCompletionAtPrimeEquivOfStabilizerLe_mapₐ (hH : MulAction.stabilizer G 𝔪 ≤ H)
    (Aₚ : Type*) [CommRing Aₚ] [Algebra A Aₚ] [𝔭.IsPrime] [IsLocalization.AtPrime Aₚ 𝔭]
    [IsLocalRing Aₚ] (B_𝔮 : Type*) [CommRing B_𝔮] [Algebra B B_𝔮] [Algebra A B_𝔮]
    [IsScalarTower A B B_𝔮] [𝔮.IsPrime] [IsLocalization.AtPrime B_𝔮 𝔮] [IsLocalRing B_𝔮]
    (x : AdicCompletion 𝔭 A) :
    adicCompletionAtPrimeEquivOfStabilizerLe H 𝔭 𝔮 𝔪 hH Aₚ B_𝔮
        (AdicCompletion.mapₐ (Algebra.ofId A Aₚ)
          ((IsLocalization.AtPrime.map_eq_maximalIdeal 𝔭 Aₚ) ▸ Ideal.le_comap_map) x) =
      AdicCompletion.mapₐ (Algebra.ofId B B_𝔮)
        ((IsLocalization.AtPrime.map_eq_maximalIdeal 𝔮 B_𝔮) ▸ Ideal.le_comap_map)
        (adicCompletionEquivOfStabilizerLe H 𝔭 𝔮 𝔪 hH x) := by
  have := Algebra.IsInvariant.isIntegral A S G; have := Algebra.IsInvariant.isIntegral B S H
  have : 𝔭.IsMaximal := ‹𝔪.LiesOver 𝔭›.over ▸ Ideal.isMaximal_under_of_isIntegral_of_isMaximal 𝔪
  have : 𝔮.IsMaximal := ‹𝔪.LiesOver 𝔮›.over ▸ Ideal.isMaximal_under_of_isIntegral_of_isMaximal 𝔪
  have hx := (AdicCompletion.equivMaximalIdealOfAtPrime 𝔭 Aₚ).symm_apply_eq.mpr
    (AdicCompletion.equivMaximalIdealOfAtPrime_apply 𝔭 Aₚ x).symm
  rw [adicCompletionAtPrimeEquivOfStabilizerLe]
  simp only [AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply,
    AdicCompletion.equivMaximalIdealOfAtPrime_apply, hx]

/-- When `𝔭` and `𝔮` are maximal, `adicCompletionAtPrimeEquivOfStabilizerLe` conjugates
`adicCompletionEquivOfStabilizerLe` by `AdicCompletion.equivMaximalIdealOfAtPrime`. -/
theorem adicCompletionAtPrimeEquivOfStabilizerLe_apply (hH : MulAction.stabilizer G 𝔪 ≤ H)
    (Aₚ : Type*) [CommRing Aₚ] [Algebra A Aₚ] [𝔭.IsMaximal] [IsLocalization.AtPrime Aₚ 𝔭]
    [IsLocalRing Aₚ] (B_𝔮 : Type*) [CommRing B_𝔮] [Algebra B B_𝔮] [Algebra A B_𝔮]
    [IsScalarTower A B B_𝔮] [𝔮.IsMaximal] [IsLocalization.AtPrime B_𝔮 𝔮] [IsLocalRing B_𝔮]
    (z : AdicCompletion (IsLocalRing.maximalIdeal Aₚ) Aₚ) :
    adicCompletionAtPrimeEquivOfStabilizerLe H 𝔭 𝔮 𝔪 hH Aₚ B_𝔮 z =
      AdicCompletion.equivMaximalIdealOfAtPrime 𝔮 B_𝔮
        (adicCompletionEquivOfStabilizerLe H 𝔭 𝔮 𝔪 hH
          ((AdicCompletion.equivMaximalIdealOfAtPrime 𝔭 Aₚ).symm z)) := by
  rw [adicCompletionAtPrimeEquivOfStabilizerLe, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    AlgEquiv.restrictScalars_apply]

/-- **Local regularity comparison across stabilizer quotients.** Under the hypotheses of
`mapₐ_ofId_bijective_of_stabilizer_le`, for any localizations `Aₚ` of `A` at `𝔭` and `B_𝔮` of `B`
at `𝔮`, `Aₚ` is a regular local ring if and only if `B_𝔮` is. -/
theorem isRegularLocalRing_atPrime_iff_of_stabilizer_le (hH : MulAction.stabilizer G 𝔪 ≤ H)
    (Aₚ : Type*) [CommRing Aₚ] [Algebra A Aₚ] [𝔭.IsPrime] [IsLocalization.AtPrime Aₚ 𝔭]
    [IsLocalRing Aₚ] (B_𝔮 : Type*) [CommRing B_𝔮] [Algebra B B_𝔮] [𝔮.IsPrime]
    [IsLocalization.AtPrime B_𝔮 𝔮] [IsLocalRing B_𝔮] :
    IsRegularLocalRing Aₚ ↔ IsRegularLocalRing B_𝔮 := by
  have := Algebra.IsInvariant.isIntegral A S G; have := Algebra.IsInvariant.isIntegral B S H
  have : 𝔭.IsMaximal := ‹𝔪.LiesOver 𝔭›.over ▸ Ideal.isMaximal_under_of_isIntegral_of_isMaximal 𝔪
  have : 𝔮.IsMaximal := ‹𝔪.LiesOver 𝔮›.over ▸ Ideal.isMaximal_under_of_isIntegral_of_isMaximal 𝔪
  have : IsNoetherian A S := isNoetherian_of_isNoetherianRing_of_finite A S
  have : IsNoetherianRing B := isNoetherian_of_tower A
    (isNoetherian_of_injective (IsScalarTower.toAlgHom A B S).toLinearMap
      (FaithfulSMul.algebraMap_injective B S))
  let e := (adicCompletionEquivOfStabilizerLe H 𝔭 𝔮 𝔪 hH).toRingEquiv
  rw [← TauCeti.AdicCompletion.isRegularLocalRing_iff_of_isMaximal 𝔭 Aₚ,
    ← TauCeti.AdicCompletion.isRegularLocalRing_iff_of_isMaximal 𝔮 B_𝔮]
  exact ⟨fun _ ↦ .of_ringEquiv e, fun _ ↦ .of_ringEquiv e.symm⟩

end QuotientComparison

end TauCeti.Algebra.IsInvariant
