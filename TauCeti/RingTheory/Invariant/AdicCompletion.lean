/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import TauCeti.RingTheory.AdicCompletion.Localization
public import TauCeti.RingTheory.Invariant.Basic

import Mathlib.RingTheory.AdicCompletion.Exactness
import TauCeti.RingTheory.AdicCompletion.CofinalLimit
import TauCeti.RingTheory.AdicCompletion.Coprime
import TauCeti.RingTheory.AdicCompletion.Extended
import TauCeti.RingTheory.AdicCompletion.LocalRing

/-!
# Adic completions of invariant rings and completed-local quotient comparison

Let a finite group `G` act on a commutative ring `S` by ring automorphisms, and let `A` be a
Noetherian invariant base ring (`[Algebra.IsInvariant A S G] [FaithfulSMul A S]`) over which `S` is
a finite module. All results in this file are characteristic-free: `#G` need not be invertible in
`A` or `S`.

## Global completion along an invariant ideal

For any ideal `I` of `A`, exactness of `I`-adic completion on finite `A`-modules
(`AdicCompletion.map_injective`, `AdicCompletion.map_exact`) applied to the invariance-defect
sequence `0 → A → S → S^{#G}` and transported along `AdicCompletion.mapAlgebraMapLinearEquiv` shows
that the canonical map `AdicCompletion I A →ₐ[A] AdicCompletion (I.map (algebraMap A S)) S` is
injective with image the elements fixed by every `g : G`.

## Decomposition-group invariants at a maximal ideal

Let `𝔪` be a maximal ideal of `S` lying over `𝔭` in `A`. The `G`-orbit `O` of `𝔪` consists of
finitely many pairwise coprime maximal ideals whose intersection `J = ⨅ Q : O, Q.1` is `G`-stable
with contraction `𝔭`, so some power of `J` lies in `𝔭 S` (`Ideal.pow_card_mem_map_under`). Combining
cofinal invariance (`AdicCompletion.mapₐ_id_bijective_of_pow_le`), the coprime product decomposition
(`AdicCompletion.coprimeEquiv`), and Shapiro's lemma on the transitive `G`-set `O` shows that
`AdicCompletion 𝔭 A →ₐ[A] AdicCompletion 𝔪 S` is injective with image the elements fixed by the
decomposition group `MulAction.stabilizer G 𝔪`.

## Completed-local quotient comparison

Consequently, for any subgroup `H` containing `MulAction.stabilizer G 𝔪` and any intermediate
`H`-invariant ring `B` between `A` and `S` with `𝔪` lying over `𝔮` in `B`, both `AdicCompletion 𝔭 A`
and `AdicCompletion 𝔮 B` map bijectively onto the same fixed subring of `AdicCompletion 𝔪 S`. Hence
`AdicCompletion 𝔭 A →ₐ[A] AdicCompletion 𝔮 B` is an isomorphism, the completed localizations at `𝔭`
and `𝔮` are canonically isomorphic, and `Localization.AtPrime 𝔭` is a regular local ring if and only
if `Localization.AtPrime 𝔮` is. Geometrically, quotienting by `G` versus by the stabilizer of a
closed point is a formal-local isomorphism at that point.

## Main definitions and results

* `TauCeti.Algebra.IsInvariant.mapₐ_algebraOfId_injective` and
  `TauCeti.Algebra.IsInvariant.mem_range_mapₐ_algebraOfId_iff`: `AdicCompletion I A` embeds into
  `AdicCompletion (I S) S` as the `G`-fixed subring.
* `TauCeti.Algebra.IsInvariant.mapₐ_maximalIdeal_injective` and
  `TauCeti.Algebra.IsInvariant.mem_range_mapₐ_maximalIdeal_iff`: `AdicCompletion 𝔭 A` embeds into
  `AdicCompletion 𝔪 S` as the `(MulAction.stabilizer G 𝔪)`-fixed subring.
* `TauCeti.Algebra.IsInvariant.bijective_mapₐ_of_stabilizer_le` and
  `TauCeti.Algebra.IsInvariant.adicCompletionEquivOfStabilizerLe`: completed-local isomorphism
  `AdicCompletion 𝔭 A ≃ₐ[A] AdicCompletion 𝔮 B` whenever `MulAction.stabilizer G 𝔪 ≤ H`.
* `TauCeti.Algebra.IsInvariant.adicCompletionAtPrimeEquivOfStabilizerLe`: completed-stalk
  isomorphism between the localizations at `𝔭` and `𝔮`.
* `TauCeti.Algebra.IsInvariant.isRegularLocalRing_atPrime_iff_of_stabilizer_le`: local regularity
  descent/ascent between `A_𝔭` and `B_𝔮`.

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

section ActionHelpers

/-- Extending an ideal of `A` to `S` gives an ideal stable under any `A`-linear action of `G`. -/
theorem map_le_comap_toAlgHom {A S G : Type*} [CommSemiring A] [Semiring S] [Algebra A S]
    [Monoid G] [MulSemiringAction G S] [SMulCommClass G A S] (I : Ideal A) (g : G) :
    I.map (algebraMap A S) ≤ (I.map (algebraMap A S)).comap (MulSemiringAction.toAlgHom A S g) :=
  Ideal.map_le_iff_le_comap.mpr fun a ha ↦
    Ideal.mem_comap.mpr (Ideal.mem_comap.mpr
      (((MulSemiringAction.toAlgHom A S g).commutes a).symm ▸
        Ideal.mem_map_of_mem (algebraMap A S) ha))

/-- An element of `MulAction.stabilizer G 𝔪` maps `𝔪` into itself via `MulSemiringAction.toAlgHom`.
-/
theorem le_comap_toAlgHom_of_mem_stabilizer {A S G : Type*} [CommSemiring A] [Semiring S]
    [Algebra A S] [Group G] [MulSemiringAction G S] [SMulCommClass G A S] {𝔪 : Ideal S} {g : G}
    (hg : g ∈ MulAction.stabilizer G 𝔪) :
    𝔪 ≤ 𝔪.comap (MulSemiringAction.toAlgHom A S g) := by
  have hg' : g • 𝔪 = 𝔪 := MulAction.mem_stabilizer_iff.mp hg
  intro s hs
  rw [Ideal.mem_comap, MulSemiringAction.toAlgHom_apply, ← hg']
  exact Ideal.smul_mem_pointwise_smul g s 𝔪 hs

private theorem mapₐ_congr {R₁ R₂ S S' : Type*} [CommRing R₁] [CommRing R₂]
    [CommRing S] [CommRing S'] [Algebra R₁ S] [Algebra R₁ S'] [Algebra R₂ S] [Algebra R₂ S']
    {I : Ideal S} {I' : Ideal S'} {f₁ : S →ₐ[R₁] S'} {hf₁ : I ≤ I'.comap f₁}
    {f₂ : S →ₐ[R₂] S'} {hf₂ : I ≤ I'.comap f₂} (h : ∀ s, f₁ s = f₂ s) (x : AdicCompletion I S) :
    AdicCompletion.mapₐ f₁ hf₁ x = AdicCompletion.mapₐ f₂ hf₂ x :=
  AdicCompletion.ext_evalₐ fun n ↦ by
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
    simp [← hs, h]

end ActionHelpers

section FixedSubalgebraSameUniverse

variable (A S G : Type*) [CommRing A] [CommRing S] [Algebra A S]
  [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G A S]

private noncomputable def defectMap :
    S →ₗ[FixedPoints.subalgebra A S G] Fin (Nat.card G) → S :=
  let eG := (Finite.equivFin G).symm
  LinearMap.pi fun i ↦
    (MulSemiringAction.toAlgHom (FixedPoints.subalgebra A S G) S (eG i)).toLinearMap - LinearMap.id

private theorem proj_comp_defectMap (i : Fin (Nat.card G)) :
    LinearMap.proj i ∘ₗ defectMap A S G =
      (MulSemiringAction.toAlgHom (FixedPoints.subalgebra A S G) S
        ((Finite.equivFin G).symm i)).toLinearMap - LinearMap.id :=
  LinearMap.ext fun _ ↦ rfl

private theorem exact_algebraLinearMap_defectMap :
    Function.Exact (Algebra.linearMap (FixedPoints.subalgebra A S G) S) (defectMap A S G) := by
  intro s
  refine ⟨fun hs ↦ ⟨⟨s, fun g ↦ ?_⟩, rfl⟩, ?_⟩
  · simpa [defectMap, sub_eq_zero] using congrFun hs (Finite.equivFin G g)
  · rintro ⟨a, rfl⟩
    ext i
    simpa [defectMap, sub_eq_zero] using a.2 ((Finite.equivFin G).symm i)

private theorem mem_range_map_algebraLinearMap_subalgebra_iff
    [IsNoetherianRing (FixedPoints.subalgebra A S G)]
    [Module.Finite (FixedPoints.subalgebra A S G) S]
    (I₀ : Ideal (FixedPoints.subalgebra A S G)) (y : AdicCompletion I₀ S) :
    y ∈ Set.range (AdicCompletion.map I₀ (Algebra.linearMap (FixedPoints.subalgebra A S G) S)) ↔
      ∀ g : G,
        AdicCompletion.map I₀
          (MulSemiringAction.toAlgHom (FixedPoints.subalgebra A S G) S g).toLinearMap y = y := by
  have hexact₀ :
      Function.Exact (Algebra.linearMap (FixedPoints.subalgebra A S G) S)
        (defectMap A S G).rangeRestrict :=
    fun s ↦ Subtype.ext_iff.trans (exact_algebraLinearMap_defectMap A S G s)
  have hexact := AdicCompletion.map_exact (I := I₀) (fun _ _ h ↦ Subtype.ext h) hexact₀
    (LinearMap.surjective_rangeRestrict (defectMap A S G))
  have hinj_sub :
      Function.Injective (AdicCompletion.map I₀ (LinearMap.range (defectMap A S G)).subtype) :=
    AdicCompletion.map_injective I₀ Subtype.val_injective
  have hsub : (LinearMap.range (defectMap A S G)).subtype ∘ₗ (defectMap A S G).rangeRestrict =
      defectMap A S G := LinearMap.ext fun _ ↦ rfl
  rw [← hexact y, ← hinj_sub.eq_iff, map_zero, AdicCompletion.map_comp_apply, hsub]
  refine ⟨fun hy g ↦ ?_, fun hy ↦ ?_⟩
  · have hi : AdicCompletion.map I₀
        (LinearMap.proj (Finite.equivFin G g) ∘ₗ defectMap A S G) y = 0 := by
      rw [← AdicCompletion.map_comp_apply, hy, map_zero]
    rwa [proj_comp_defectMap, Equiv.symm_apply_apply, map_sub, LinearMap.sub_apply,
      AdicCompletion.map_id, LinearMap.id_apply, sub_eq_zero] at hi
  · apply (AdicCompletion.piEquivOfFintype I₀ (fun _ : Fin (Nat.card G) ↦ S)).injective
    rw [map_zero, AdicCompletion.piEquivOfFintype_apply]
    funext i
    rw [Pi.zero_apply, AdicCompletion.pi, LinearMap.pi_apply, AdicCompletion.map_comp_apply,
      proj_comp_defectMap, map_sub, LinearMap.sub_apply, AdicCompletion.map_id,
      LinearMap.id_apply, sub_eq_zero]
    exact hy _

end FixedSubalgebraSameUniverse

section GlobalIdeal

variable {A S : Type*} (G : Type*) [CommRing A] [CommRing S] [Algebra A S]
  [Group G] [MulSemiringAction G S] [SMulCommClass G A S] [FaithfulSMul A S]

/-- When `A → S` is a faithful `G`-invariant extension, `A` is canonically `A`-isomorphic to
`FixedPoints.subalgebra A S G` (which lives in the universe of `S`). -/
private noncomputable def fixedSubalgebraAlgEquiv [Algebra.IsInvariant A S G] :
    A ≃ₐ[A] FixedPoints.subalgebra A S G :=
  AlgEquiv.ofBijective (Algebra.ofId A (FixedPoints.subalgebra A S G))
    ⟨fun _ _ h ↦ FaithfulSMul.algebraMap_injective A S (congrArg Subtype.val h),
      fun d ↦ let ⟨a, ha⟩ := Algebra.IsInvariant.isInvariant (A := A) (G := G) d.1 d.2
        ⟨a, Subtype.ext ha⟩⟩

private theorem coe_fixedSubalgebraAlgEquiv [Algebra.IsInvariant A S G] (a : A) :
    ((fixedSubalgebraAlgEquiv (A := A) (S := S) G a : FixedPoints.subalgebra A S G) : S) =
      algebraMap A S a :=
  (IsScalarTower.algebraMap_apply A (FixedPoints.subalgebra A S G) S a).symm

private theorem map_fixedSubalgebraAlgEquiv_map [Algebra.IsInvariant A S G] (I : Ideal A) :
    (I.map (fixedSubalgebraAlgEquiv (A := A) (S := S) G)).map
      (algebraMap (FixedPoints.subalgebra A S G) S) = I.map (algebraMap A S) :=
  le_antisymm
    (Ideal.map_le_iff_le_comap.mpr <| Ideal.map_le_iff_le_comap.mpr fun a ha ↦
      Ideal.mem_comap.mpr <| Ideal.mem_comap.mpr <|
        coe_fixedSubalgebraAlgEquiv (S := S) G a ▸ Ideal.mem_map_of_mem _ ha)
    (Ideal.map_le_iff_le_comap.mpr fun a ha ↦ Ideal.mem_comap.mpr <|
      coe_fixedSubalgebraAlgEquiv (S := S) G a ▸
        Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ ha))

private theorem map_algEquiv_refl {R : Type*} [CommRing R] (J : Ideal R) :
    J.map (AlgEquiv.refl : R ≃ₐ[R] R) = J :=
  le_antisymm (Ideal.map_le_iff_le_comap.mpr fun _ h ↦ Ideal.mem_comap.mpr h)
    fun _ h ↦ Ideal.mem_map_of_mem _ h

variable (S) in
private noncomputable def extendedSubalgebraEquiv [Algebra.IsInvariant A S G] (I : Ideal A) :
    AdicCompletion (I.map (fixedSubalgebraAlgEquiv (A := A) (S := S) G)) S
      ≃ₗ[FixedPoints.subalgebra A S G] AdicCompletion (I.map (algebraMap A S)) S :=
  (AdicCompletion.mapAlgebraMapLinearEquiv _ S S).trans
    ((AdicCompletion.congrₐ (AlgEquiv.refl : S ≃ₐ[S] S)
      ((map_algEquiv_refl _).trans
        (map_fixedSubalgebraAlgEquiv_map (S := S) G I))).toLinearEquiv.restrictScalars _)

private theorem extendedSubalgebraEquiv_apply [Algebra.IsInvariant A S G] (I : Ideal A)
    (y₀ : AdicCompletion (I.map (fixedSubalgebraAlgEquiv (A := A) (S := S) G)) S) :
    extendedSubalgebraEquiv S G I y₀ =
      AdicCompletion.congrₐ (AlgEquiv.refl : S ≃ₐ[S] S)
        ((map_algEquiv_refl _).trans (map_fixedSubalgebraAlgEquiv_map (S := S) G I))
        (AdicCompletion.mapAlgebraMapLinearEquiv _ S S y₀) :=
  rfl

private theorem extendedSubalgebraEquiv_map_algebraLinearMap [Algebra.IsInvariant A S G]
    (I : Ideal A) (hle : I ≤ (I.map (algebraMap A S)).comap (Algebra.ofId A S))
    (x : AdicCompletion I A) :
    extendedSubalgebraEquiv S G I
      (AdicCompletion.map _ (Algebra.linearMap (FixedPoints.subalgebra A S G) S)
        (AdicCompletion.congrₐ (fixedSubalgebraAlgEquiv (A := A) (S := S) G) rfl x)) =
      AdicCompletion.mapₐ (Algebra.ofId A S) hle x := by
  rw [extendedSubalgebraEquiv_apply, AdicCompletion.mapAlgebraMapLinearEquiv_map_algebraLinearMap]
  exact AdicCompletion.ext_evalₐ fun n ↦ by
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
    simp [← ha, coe_fixedSubalgebraAlgEquiv]

private theorem extendedSubalgebraEquiv_map_toAlgHom [Algebra.IsInvariant A S G] (I : Ideal A)
    (hg_le : ∀ g : G,
      I.map (algebraMap A S) ≤ (I.map (algebraMap A S)).comap (MulSemiringAction.toAlgHom A S g))
    (g : G) (y₀ : AdicCompletion (I.map (fixedSubalgebraAlgEquiv (A := A) (S := S) G)) S) :
    extendedSubalgebraEquiv S G I
      (AdicCompletion.map _
        (MulSemiringAction.toAlgHom (FixedPoints.subalgebra A S G) S g).toLinearMap y₀) =
      AdicCompletion.mapₐ (MulSemiringAction.toAlgHom A S g) (hg_le g)
        (extendedSubalgebraEquiv S G I y₀) := by
  rw [extendedSubalgebraEquiv_apply, extendedSubalgebraEquiv_apply,
    AdicCompletion.mapAlgebraMapLinearEquiv_map_algHom _
      (MulSemiringAction.toAlgHom (FixedPoints.subalgebra A S G) S g)]
  exact AdicCompletion.ext_evalₐ fun n ↦ by
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective
      (AdicCompletion.evalₐ _ n (AdicCompletion.mapAlgebraMapLinearEquiv _ S S y₀))
    simp [← hs]

variable [IsNoetherianRing A] [Module.Finite A S]

/-- **Adic completion preserves injectivity of an invariant subring.** For a group `G` acting on
`S` with Noetherian invariant base ring `A` and `S` module-finite over `A`, completing `A → S`
along any ideal `I` of `A` and its extension `I S` is injective. -/
theorem mapₐ_algebraOfId_injective [Algebra.IsInvariant A S G] (I : Ideal A)
    (hle : I ≤ (I.map (algebraMap A S)).comap (Algebra.ofId A S) :=
      fun _ hx ↦ Ideal.mem_comap.mpr (Ideal.mem_map_of_mem _ hx)) :
    Function.Injective (AdicCompletion.mapₐ (Algebra.ofId A S) hle) := by
  have : IsNoetherianRing (FixedPoints.subalgebra A S G) :=
    isNoetherianRing_of_ringEquiv A (fixedSubalgebraAlgEquiv (A := A) (S := S) G).toRingEquiv
  have : Module.Finite (FixedPoints.subalgebra A S G) S :=
    Module.Finite.of_restrictScalars_finite A (FixedPoints.subalgebra A S G) S
  have hinj := AdicCompletion.map_injective (I.map (fixedSubalgebraAlgEquiv (A := A) (S := S) G))
    (f := Algebra.linearMap (FixedPoints.subalgebra A S G) S) fun _ _ h ↦ Subtype.ext h
  intro x₁ x₂ hx
  rw [← extendedSubalgebraEquiv_map_algebraLinearMap G I hle x₁,
    ← extendedSubalgebraEquiv_map_algebraLinearMap G I hle x₂] at hx
  exact (AdicCompletion.congrₐ (fixedSubalgebraAlgEquiv (A := A) (S := S) G) rfl).injective
    (hinj ((extendedSubalgebraEquiv S G I).injective hx))

variable {G} [Finite G] in
/-- **Invariants of an adic completion along an extended ideal.** Under the hypotheses of
`mapₐ_algebraOfId_injective` for a finite group `G`, the image of `AdicCompletion I A` inside
`AdicCompletion (I.map (algebraMap A S)) S` consists precisely of the elements fixed by every
`g : G`. -/
theorem mem_range_mapₐ_algebraOfId_iff [Algebra.IsInvariant A S G] (I : Ideal A)
    (hle : I ≤ (I.map (algebraMap A S)).comap (Algebra.ofId A S) :=
      fun _ hx ↦ Ideal.mem_comap.mpr (Ideal.mem_map_of_mem _ hx))
    (hg_le : ∀ g : G,
      I.map (algebraMap A S) ≤
        (I.map (algebraMap A S)).comap (MulSemiringAction.toAlgHom A S g) :=
      map_le_comap_toAlgHom I)
    (y : AdicCompletion (I.map (algebraMap A S)) S) :
    y ∈ Set.range (AdicCompletion.mapₐ (Algebra.ofId A S) hle) ↔
      ∀ g : G, AdicCompletion.mapₐ (MulSemiringAction.toAlgHom A S g) (hg_le g) y = y := by
  have : IsNoetherianRing (FixedPoints.subalgebra A S G) :=
    isNoetherianRing_of_ringEquiv A (fixedSubalgebraAlgEquiv (A := A) (S := S) G).toRingEquiv
  have : Module.Finite (FixedPoints.subalgebra A S G) S :=
    Module.Finite.of_restrictScalars_finite A (FixedPoints.subalgebra A S G) S
  refine ⟨?_, fun hfix ↦ ?_⟩
  · rintro ⟨x, rfl⟩ g
    rw [AdicCompletion.mapₐ_mapₐ]
    exact mapₐ_congr ((MulSemiringAction.toAlgHom A S g).commutes) x
  · set y₀ := (extendedSubalgebraEquiv S G I).symm y
    have hy : extendedSubalgebraEquiv S G I y₀ = y := LinearEquiv.apply_symm_apply _ y
    obtain ⟨x₀, hx₀⟩ : y₀ ∈ Set.range
        (AdicCompletion.map _ (Algebra.linearMap (FixedPoints.subalgebra A S G) S)) :=
      (mem_range_map_algebraLinearMap_subalgebra_iff _ _ _ _ _).mpr fun g ↦
        (extendedSubalgebraEquiv S G I).injective <| by
          rw [extendedSubalgebraEquiv_map_toAlgHom G I hg_le g y₀, hy]; exact hfix g
    refine ⟨(AdicCompletion.congrₐ (fixedSubalgebraAlgEquiv (A := A) (S := S) G) rfl).symm x₀, ?_⟩
    rw [← extendedSubalgebraEquiv_map_algebraLinearMap G I hle, AlgEquiv.apply_symm_apply, hx₀, hy]

end GlobalIdeal

section MaximalIdeal

variable {A S : Type*} (G : Type*) [CommRing A] [CommRing S] [Algebra A S]
  [Group G] [MulSemiringAction G S] [SMulCommClass G A S]
  (𝔭 : Ideal A) (𝔪 : Ideal S)

private theorem isMaximal_orbit [𝔪.IsMaximal] (Q : MulAction.orbit G 𝔪) : Q.1.IsMaximal := by
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp Q.2
  rw [← hg, 𝔪.pointwise_smul_eq_comap]
  infer_instance

private theorem pairwise_isCoprime_orbit [𝔪.IsMaximal] :
    Pairwise (IsCoprime on fun Q : MulAction.orbit G 𝔪 ↦ Q.1) := fun Q₁ Q₂ hne ↦ by
  have := isMaximal_orbit G 𝔪 Q₁; have := isMaximal_orbit G 𝔪 Q₂
  exact Ideal.isCoprime_of_isMaximal (Subtype.coe_ne_coe.mpr hne)

private def orbitInf : Ideal S :=
  ⨅ Q : MulAction.orbit G 𝔪, Q.1

private theorem inv_smul_mem_orbit (g : G) (Q : MulAction.orbit G 𝔪) :
    g⁻¹ • Q.1 ∈ MulAction.orbit G 𝔪 := by
  obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.mp Q.2
  exact MulAction.mem_orbit_iff.mpr ⟨g⁻¹ * h, by rw [mul_smul, hh]⟩

private theorem orbitInf_stable (g : G) {s : S} (hs : s ∈ orbitInf G 𝔪) :
    g • s ∈ orbitInf G 𝔪 :=
  Ideal.mem_iInf.mpr fun Q ↦
    Ideal.mem_inv_pointwise_smul_iff.mp
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

/-- The canonical `A`-algebra map from `AdicCompletion (𝔭 S) S` to the product of completions along
the `G`-orbit of `𝔪`. -/
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
  exact mapₐ_congr (fun _ ↦ rfl) y

variable [Finite G] [FaithfulSMul A S] [IsNoetherianRing A] [Module.Finite A S]
  [𝔪.IsMaximal] [𝔪.LiesOver 𝔭]

omit [FaithfulSMul A S] [𝔪.IsMaximal] in
private theorem exists_orbitInf_pow_le_map [Algebra.IsInvariant A S G] :
    ∃ k : ℕ, orbitInf G 𝔪 ^ k ≤ 𝔭.map (algebraMap A S) := by
  have : IsNoetherian A S := isNoetherian_of_isNoetherianRing_of_finite A S
  refine Ideal.exists_pow_le_of_le_radical_of_fg
    (fun b hb ↦ ⟨Nat.card G, under_orbitInf G 𝔭 𝔪 ▸
      Ideal.pow_card_mem_map_under A G (orbitInf_stable G 𝔪) hb⟩)
    ((IsNoetherian.noetherian ((orbitInf G 𝔪).restrictScalars A)).of_restrictScalars A)

omit [FaithfulSMul A S] in
private theorem orbitPiMapₐ_bijective [Algebra.IsInvariant A S G] :
    Function.Bijective (orbitPiMapₐ G 𝔭 𝔪) := by
  have : Finite (MulAction.orbit G 𝔪) := (Set.finite_range _).to_subtype
  exact (AdicCompletion.bijective_pi_mapₐ (fun Q : MulAction.orbit G 𝔪 ↦ Q.1)
    (pairwise_isCoprime_orbit G 𝔪)).comp
    (AdicCompletion.mapₐ_id_bijective_of_pow_le
      (fun _ hx ↦ Ideal.mem_comap.mpr (map_le_orbitInf G 𝔭 𝔪 hx))
      (exists_orbitInf_pow_le_map G 𝔭 𝔪))

/-- **Completed invariant ring injects into completion at a maximal ideal.** Under the hypotheses
of `mapₐ_algebraOfId_injective` for a finite group `G`, if `𝔪` is a maximal ideal of `S` lying over
`𝔭` in `A`, then `AdicCompletion 𝔭 A →ₐ[A] AdicCompletion 𝔪 S` is injective. -/
theorem mapₐ_maximalIdeal_injective [Algebra.IsInvariant A S G]
    (h𝔭𝔪 : 𝔭 ≤ 𝔪.comap (Algebra.ofId A S) :=
      fun a ha ↦ Ideal.mem_comap.mpr ((𝔪.mem_of_liesOver 𝔭 a).mp ha)) :
    Function.Injective (AdicCompletion.mapₐ (Algebra.ofId A S) h𝔭𝔪) := by
  have hle : 𝔭 ≤ (𝔭.map (algebraMap A S)).comap (Algebra.ofId A S) :=
    fun _ hx ↦ Ideal.mem_comap.mpr (Ideal.mem_map_of_mem _ hx)
  intro x₁ x₂ hx
  apply mapₐ_algebraOfId_injective G 𝔭 hle
  apply (orbitPiMapₐ_bijective G 𝔭 𝔪).injective
  funext Q
  obtain ⟨g, hgQ⟩ := MulAction.mem_orbit_iff.mp Q.2
  have hcoord (x : AdicCompletion 𝔭 A) :
      orbitPiMapₐ G 𝔭 𝔪 (AdicCompletion.mapₐ (Algebra.ofId A S) hle x) Q =
        AdicCompletion.mapₐ (MulSemiringAction.toAlgHom A S g)
          (fun s hs ↦ Ideal.mem_comap.mpr (hgQ ▸ Ideal.smul_mem_pointwise_smul g s 𝔪 hs))
          (AdicCompletion.mapₐ (Algebra.ofId A S) h𝔭𝔪 x) := by
    rw [orbitPiMapₐ_eq_mapₐ, AdicCompletion.mapₐ_mapₐ, AdicCompletion.mapₐ_mapₐ]
    exact mapₐ_congr (fun a ↦ ((MulSemiringAction.toAlgHom A S g).commutes a).symm) x
  rw [hcoord x₁, hcoord x₂, hx]

omit [Finite G] [FaithfulSMul A S] [IsNoetherianRing A] [Module.Finite A S] [𝔪.IsMaximal] in
private theorem orbitPiMapₐ_mapₐ_toAlgHom (g : G)
    (y : AdicCompletion (𝔭.map (algebraMap A S)) S) (Q : MulAction.orbit G 𝔪) :
    orbitPiMapₐ G 𝔭 𝔪
      (AdicCompletion.mapₐ (MulSemiringAction.toAlgHom A S g) (map_le_comap_toAlgHom 𝔭 g) y) Q =
      AdicCompletion.mapₐ (MulSemiringAction.toAlgHom A S g)
        (fun _ hs ↦ Ideal.mem_comap.mpr (Ideal.mem_inv_pointwise_smul_iff.mp hs))
        (orbitPiMapₐ G 𝔭 𝔪 y ⟨g⁻¹ • Q.1, inv_smul_mem_orbit G 𝔪 g Q⟩) := by
  rw [orbitPiMapₐ_eq_mapₐ, orbitPiMapₐ_eq_mapₐ, AdicCompletion.mapₐ_mapₐ, AdicCompletion.mapₐ_mapₐ]
  exact mapₐ_congr (fun _ ↦ rfl) y

variable {G} in
/-- **Decomposition-group invariants of the completion at a maximal ideal.** Under the hypotheses
of `mapₐ_maximalIdeal_injective`, the image of `AdicCompletion 𝔭 A` inside `AdicCompletion 𝔪 S`
consists precisely of the elements fixed by every `g ∈ MulAction.stabilizer G 𝔪`. -/
theorem mem_range_mapₐ_maximalIdeal_iff [Algebra.IsInvariant A S G]
    (h𝔭𝔪 : 𝔭 ≤ 𝔪.comap (Algebra.ofId A S) :=
      fun a ha ↦ Ideal.mem_comap.mpr ((𝔪.mem_of_liesOver 𝔭 a).mp ha))
    (z : AdicCompletion 𝔪 S) :
    z ∈ Set.range (AdicCompletion.mapₐ (Algebra.ofId A S) h𝔭𝔪) ↔
      ∀ g (hg : g ∈ MulAction.stabilizer G 𝔪),
        AdicCompletion.mapₐ (MulSemiringAction.toAlgHom A S g)
          (le_comap_toAlgHom_of_mem_stabilizer hg) z = z := by
  refine ⟨?_, fun hz ↦ ?_⟩
  · rintro ⟨x, rfl⟩ g hg
    rw [AdicCompletion.mapₐ_mapₐ]
    exact mapₐ_congr ((MulSemiringAction.toAlgHom A S g).commutes) x
  · have hle : 𝔭 ≤ (𝔭.map (algebraMap A S)).comap (Algebra.ofId A S) :=
      fun _ hx ↦ Ideal.mem_comap.mpr (Ideal.mem_map_of_mem _ hx)
    -- Spread `z` equivariantly across the `G`-orbit of `𝔪` using orbit representatives.
    choose γ hγ using fun Q : MulAction.orbit G 𝔪 ↦ MulAction.mem_orbit_iff.mp Q.2
    have hγ_le (Q : MulAction.orbit G 𝔪) :
        𝔪 ≤ Q.1.comap (MulSemiringAction.toAlgHom A S (γ Q)) :=
      fun s hs ↦ Ideal.mem_comap.mpr (hγ Q ▸ Ideal.smul_mem_pointwise_smul (γ Q) s 𝔪 hs)
    let f : ∀ Q : MulAction.orbit G 𝔪, AdicCompletion Q.1 S :=
      fun Q ↦ AdicCompletion.mapₐ (MulSemiringAction.toAlgHom A S (γ Q)) (hγ_le Q) z
    obtain ⟨y, hy⟩ := (orbitPiMapₐ_bijective G 𝔭 𝔪).surjective f
    -- Show `y` is `G`-fixed by checking equivariance of `f` on `MulAction.orbit G 𝔪`.
    obtain ⟨x, rfl⟩ : y ∈ Set.range (AdicCompletion.mapₐ (Algebra.ofId A S) hle) := by
      refine (mem_range_mapₐ_algebraOfId_iff (G := G) 𝔭 hle (map_le_comap_toAlgHom 𝔭) y).mpr
        fun g ↦ (orbitPiMapₐ_bijective G 𝔭 𝔪).injective <| funext fun Q ↦ ?_
      let Q' : MulAction.orbit G 𝔪 := ⟨g⁻¹ • Q.1, inv_smul_mem_orbit G 𝔪 g Q⟩
      rw [orbitPiMapₐ_mapₐ_toAlgHom G 𝔭 𝔪 g y Q, hy]
      dsimp only [f]
      have hk_mem : (γ Q)⁻¹ * (g * γ Q') ∈ MulAction.stabilizer G 𝔪 := by
        rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hγ Q', smul_inv_smul,
          ← hγ Q, inv_smul_smul]
      conv_rhs => rw [← hz _ hk_mem]
      rw [AdicCompletion.mapₐ_mapₐ, AdicCompletion.mapₐ_mapₐ]
      exact mapₐ_congr (fun s ↦ by simp [mul_smul, Q']) z
    let Q₀ : MulAction.orbit G 𝔪 := ⟨𝔪, MulAction.mem_orbit_self 𝔪⟩
    have hf₀ : f Q₀ = z := hz (γ Q₀) (MulAction.mem_stabilizer_iff.mpr (hγ Q₀))
    refine ⟨x, (?_ : AdicCompletion.mapₐ (Algebra.ofId A S) h𝔭𝔪 x =
      orbitPiMapₐ G 𝔭 𝔪 (AdicCompletion.mapₐ (Algebra.ofId A S) hle x) Q₀).trans
      ((congrFun hy Q₀).trans hf₀)⟩
    rw [orbitPiMapₐ_eq_mapₐ, AdicCompletion.mapₐ_mapₐ]
    exact mapₐ_congr (fun _ ↦ rfl) x

end MaximalIdeal

section QuotientComparison

private theorem isNoetherianRing_intermediate (A B S : Type*) [CommRing A] [CommRing B] [CommRing S]
    [Algebra A B] [Algebra B S] [Algebra A S] [IsScalarTower A B S]
    [IsNoetherianRing A] [Module.Finite A S] [FaithfulSMul B S] : IsNoetherianRing B := by
  have : IsNoetherian A S := isNoetherian_of_isNoetherianRing_of_finite A S
  have : IsNoetherian A B :=
    isNoetherian_of_linearEquiv
      (LinearEquiv.ofInjective (IsScalarTower.toAlgHom A B S).toLinearMap
        (FaithfulSMul.algebraMap_injective B S)).symm
  exact (isNoetherianRing_iff_ideal_fg B).mpr fun I ↦
    (IsNoetherian.noetherian (I.restrictScalars A)).of_restrictScalars A

private theorem mapₐ_toAlgHom_subgroup_eq {S G : Type*} [CommRing S] [Group G]
    [MulSemiringAction G S] (𝔪 : Ideal S) (A B : Type*) [CommRing A] [CommRing B]
    [Algebra A S] [Algebra B S] [SMulCommClass G A S] (H : Subgroup G) [SMulCommClass H B S]
    {g : G} (hg : g ∈ MulAction.stabilizer G 𝔪) (h : H) (hhG : (h : G) = g)
    (hh : h ∈ MulAction.stabilizer H 𝔪) (z : AdicCompletion 𝔪 S) :
    AdicCompletion.mapₐ (MulSemiringAction.toAlgHom A S g)
        (le_comap_toAlgHom_of_mem_stabilizer hg) z =
      AdicCompletion.mapₐ (MulSemiringAction.toAlgHom B S h)
        (le_comap_toAlgHom_of_mem_stabilizer hh) z :=
  mapₐ_congr (fun s ↦ by simp [← hhG, Subgroup.smul_def]) z

variable {A B S G : Type*} [CommRing A] [CommRing B] [CommRing S]
  [Algebra A B] [Algebra B S] [Algebra A S] [IsScalarTower A B S]
  [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G A S]
  [Algebra.IsInvariant A S G] [FaithfulSMul A S] [IsNoetherianRing A] [Module.Finite A S]
  (H : Subgroup G) [SMulCommClass H B S] [Algebra.IsInvariant B S H] [FaithfulSMul B S]
  (𝔭 : Ideal A) (𝔮 : Ideal B) (𝔪 : Ideal S) [𝔪.IsMaximal] [𝔪.LiesOver 𝔭] [𝔪.LiesOver 𝔮]

/-- **Completed-local quotient comparison.** If `H ≤ G` contains the decomposition group
`MulAction.stabilizer G 𝔪` of a maximal ideal `𝔪` of `S`, and `B` is an `H`-invariant intermediate
ring between `A` and `S` with `𝔪` lying over `𝔮` in `B` and `𝔭` in `A`, then the canonical map
`AdicCompletion 𝔭 A →ₐ[A] AdicCompletion 𝔮 B` is bijective. -/
theorem bijective_mapₐ_of_stabilizer_le (hH : MulAction.stabilizer G 𝔪 ≤ H)
    (h𝔭𝔮 : 𝔭 ≤ 𝔮.comap (Algebra.ofId A B) :=
      (have := Ideal.LiesOver.tower_bot 𝔪 𝔮 𝔭;
        fun a ha ↦ Ideal.mem_comap.mpr ((𝔮.mem_of_liesOver 𝔭 a).mp ha))) :
    Function.Bijective (AdicCompletion.mapₐ (Algebra.ofId A B) h𝔭𝔮) := by
  have : IsNoetherianRing B := isNoetherianRing_intermediate A B S
  have : Module.Finite B S := Module.Finite.of_restrictScalars_finite A B S
  have h𝔮𝔪 : 𝔮 ≤ 𝔪.comap (Algebra.ofId B S) :=
    fun b hb ↦ Ideal.mem_comap.mpr ((𝔪.mem_of_liesOver 𝔮 b).mp hb)
  have h𝔭𝔪 : 𝔭 ≤ 𝔪.comap (Algebra.ofId A S) :=
    fun a ha ↦ Ideal.mem_comap.mpr ((𝔪.mem_of_liesOver 𝔭 a).mp ha)
  have hcomp (x : AdicCompletion 𝔭 A) :
      AdicCompletion.mapₐ (Algebra.ofId B S) h𝔮𝔪 (AdicCompletion.mapₐ (Algebra.ofId A B) h𝔭𝔮 x) =
        AdicCompletion.mapₐ (Algebra.ofId A S) h𝔭𝔪 x :=
    AdicCompletion.ext_evalₐ fun n ↦ by
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ 𝔭 n x)
      simp [← ha, ← IsScalarTower.algebraMap_apply A B S]
  refine ⟨fun x₁ x₂ hx ↦ mapₐ_maximalIdeal_injective G 𝔭 𝔪 h𝔭𝔪 ?_, fun y ↦ ?_⟩
  · rw [← hcomp x₁, ← hcomp x₂, hx]
  · set z : AdicCompletion 𝔪 S := AdicCompletion.mapₐ (Algebra.ofId B S) h𝔮𝔪 y
    have hzH := (mem_range_mapₐ_maximalIdeal_iff (G := H) 𝔮 𝔪 h𝔮𝔪 z).mp ⟨y, rfl⟩
    have hzG : z ∈ Set.range (AdicCompletion.mapₐ (Algebra.ofId A S) h𝔭𝔪) := by
      refine (mem_range_mapₐ_maximalIdeal_iff (G := G) 𝔭 𝔪 h𝔭𝔪 z).mpr fun g hg ↦ ?_
      let h : H := ⟨g, hH hg⟩
      have hh : h ∈ MulAction.stabilizer H 𝔪 :=
        MulAction.mem_stabilizer_iff.mpr (MulAction.mem_stabilizer_iff.mp hg)
      exact (mapₐ_toAlgHom_subgroup_eq 𝔪 A B H hg h rfl hh z).trans (hzH h hh)
    obtain ⟨x, hx⟩ := hzG
    exact ⟨x, mapₐ_maximalIdeal_injective H 𝔮 𝔪 h𝔮𝔪 ((hcomp x).trans hx)⟩

/-- Bundled `A`-algebra isomorphism `AdicCompletion 𝔭 A ≃ₐ[A] AdicCompletion 𝔮 B` when
`MulAction.stabilizer G 𝔪 ≤ H`. -/
noncomputable def adicCompletionEquivOfStabilizerLe (hH : MulAction.stabilizer G 𝔪 ≤ H) :
    AdicCompletion 𝔭 A ≃ₐ[A] AdicCompletion 𝔮 B :=
  AlgEquiv.ofBijective
    (AdicCompletion.mapₐ (Algebra.ofId A B)
      (have := Ideal.LiesOver.tower_bot 𝔪 𝔮 𝔭;
        fun a ha ↦ Ideal.mem_comap.mpr ((𝔮.mem_of_liesOver 𝔭 a).mp ha)))
    (bijective_mapₐ_of_stabilizer_le H 𝔭 𝔮 𝔪 hH)

/-- Applying `adicCompletionEquivOfStabilizerLe` agrees with
`AdicCompletion.mapₐ (Algebra.ofId A B)`. -/
@[simp]
theorem adicCompletionEquivOfStabilizerLe_apply (hH : MulAction.stabilizer G 𝔪 ≤ H)
    (x : AdicCompletion 𝔭 A) :
    adicCompletionEquivOfStabilizerLe H 𝔭 𝔮 𝔪 hH x =
      AdicCompletion.mapₐ (Algebra.ofId A B)
        (have := Ideal.LiesOver.tower_bot 𝔪 𝔮 𝔭;
          fun a ha ↦ Ideal.mem_comap.mpr ((𝔮.mem_of_liesOver 𝔭 a).mp ha))
        x := by
  rw [adicCompletionEquivOfStabilizerLe, AlgEquiv.ofBijective_apply]

/-- `adicCompletionEquivOfStabilizerLe` extends `algebraMap A B` along `AdicCompletion.of`. -/
theorem adicCompletionEquivOfStabilizerLe_of (hH : MulAction.stabilizer G 𝔪 ≤ H) (a : A) :
    adicCompletionEquivOfStabilizerLe H 𝔭 𝔮 𝔪 hH (AdicCompletion.of 𝔭 A a) =
      AdicCompletion.of 𝔮 B (algebraMap A B a) := by
  simp

/-- **Completed-stalk quotient comparison.** Under the hypotheses of
`bijective_mapₐ_of_stabilizer_le`, for any localizations `Aₚ` of `A` at `𝔭` and `B_𝔮` of `B` at `𝔮`,
their completions along their maximal ideals are canonically isomorphic as `A`-algebras. -/
noncomputable def adicCompletionAtPrimeEquivOfStabilizerLe (hH : MulAction.stabilizer G 𝔪 ≤ H)
    (Aₚ : Type*) [CommRing Aₚ] [Algebra A Aₚ]
    [𝔭.IsMaximal] [IsLocalization.AtPrime Aₚ 𝔭] [IsLocalRing Aₚ]
    (B_𝔮 : Type*) [CommRing B_𝔮] [Algebra B B_𝔮] [Algebra A B_𝔮] [IsScalarTower A B B_𝔮]
    [𝔮.IsMaximal] [IsLocalization.AtPrime B_𝔮 𝔮] [IsLocalRing B_𝔮] :
    AdicCompletion (IsLocalRing.maximalIdeal Aₚ) Aₚ ≃ₐ[A]
      AdicCompletion (IsLocalRing.maximalIdeal B_𝔮) B_𝔮 :=
  (AdicCompletion.equivMaximalIdealOfAtPrime 𝔭 Aₚ).symm.trans
    ((adicCompletionEquivOfStabilizerLe H 𝔭 𝔮 𝔪 hH).trans
      ((AdicCompletion.equivMaximalIdealOfAtPrime 𝔮 B_𝔮).restrictScalars A))

/-- **Local regularity comparison across stabilizer quotients.** Under the hypotheses of
`bijective_mapₐ_of_stabilizer_le`, `Localization.AtPrime 𝔭` is a regular local ring if and only if
`Localization.AtPrime 𝔮` is. -/
theorem isRegularLocalRing_atPrime_iff_of_stabilizer_le [𝔭.IsPrime] [𝔮.IsPrime]
    (hH : MulAction.stabilizer G 𝔪 ≤ H) :
    IsRegularLocalRing (Localization.AtPrime 𝔭) ↔
      IsRegularLocalRing (Localization.AtPrime 𝔮) := by
  have : Algebra.IsIntegral A S := Algebra.IsInvariant.isIntegral A S G
  have : Algebra.IsIntegral B S := Algebra.IsInvariant.isIntegral B S H
  have : 𝔭.IsMaximal := ‹𝔪.LiesOver 𝔭›.over ▸ Ideal.isMaximal_under_of_isIntegral_of_isMaximal 𝔪
  have : 𝔮.IsMaximal := ‹𝔪.LiesOver 𝔮›.over ▸ Ideal.isMaximal_under_of_isIntegral_of_isMaximal 𝔪
  have : IsNoetherianRing B := isNoetherianRing_intermediate A B S
  have : IsNoetherianRing (Localization.AtPrime 𝔭) :=
    IsLocalization.isNoetherianRing 𝔭.primeCompl _ inferInstance
  have : IsNoetherianRing (Localization.AtPrime 𝔮) :=
    IsLocalization.isNoetherianRing 𝔮.primeCompl _ inferInstance
  let e := (adicCompletionAtPrimeEquivOfStabilizerLe H 𝔭 𝔮 𝔪 hH
    (Localization.AtPrime 𝔭) (Localization.AtPrime 𝔮)).toRingEquiv
  rw [← TauCeti.AdicCompletion.isRegularLocalRing_iff (R := Localization.AtPrime 𝔭),
    ← TauCeti.AdicCompletion.isRegularLocalRing_iff (R := Localization.AtPrime 𝔮)]
  exact ⟨fun _ ↦ .of_ringEquiv e, fun _ ↦ .of_ringEquiv e.symm⟩

end QuotientComparison

end TauCeti.Algebra.IsInvariant
