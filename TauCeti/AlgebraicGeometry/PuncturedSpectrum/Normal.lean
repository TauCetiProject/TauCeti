/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Tilde.Hartogs
public import TauCeti.RingTheory.Etale.Normal
import TauCeti.RingTheory.Localization.Integral
import Mathlib.RingTheory.LocalProperties.Reduced

/-!
# Normality from the Hartogs property

Let `W` be an open subset of `Spec B` such that every section of `Spec B` over `W` comes from a
unique element of `B`, and such that `B_q` is an integrally closed domain at every point `q` of `W`.
Then `B` is integrally closed in each localization `E` of `B` at nonzerodivisors. Indeed, an
element `x / t` of `E` which is integral over `B` lies in `B_q` for every `q ∈ W`, these local
fractions glue to a section of `Spec B` over `W`, and the element `c` of `B` restricting to this
section satisfies `c t = x`, because `c t - x` vanishes at every point of `W`.

Combined with the normality of a ring integrally closed in a reduced Artinian ring
(`IsIntegrallyClosedIn.isDomain_localization_atPrime`), this gives normality of a finite
torsion-free algebra `B` over an integrally closed domain `A` which is étale over `A` at the points
of `W`: the generic fibre of `B` over `A` is a reduced Artinian localization of `B`.

The typical `W` is the preimage in `Spec B` of the punctured spectrum of a local ring `A`. For a
finite étale cover `V` of the punctured spectrum of a Noetherian local ring of depth at least two,
`V` is the restriction of the spectrum of `B = Γ(V, 𝒪_V)`
(`TauCeti.IsLocalRing.isPullback_puncturedSpectrum_toSpecΓ`), so restriction of sections of
`Spec B` to this preimage is bijective. If moreover `A` is an integrally closed domain and `B` is
finite and torsion free over `A` and étale over `A` at every prime not lying over the maximal ideal,
the étale form shows that `B` is normal. This is the
normality of `Γ(V, 𝒪_V)` in Stacks, Lemma 58.20.3 (0BM9), where it follows from the normality of
`V`.

## Main results

* `TauCeti.AlgebraicGeometry.Spec.isIntegrallyClosedIn_of_presheaf_map_leTop_bijective`: `B` is
  integrally closed in its localizations at nonzerodivisors.
* `TauCeti.AlgebraicGeometry.Spec.isIntegrallyClosed_of_presheaf_map_leTop_bijective`: `B` is
  integrally closed in its total ring of fractions.
* `TauCeti.AlgebraicGeometry.Spec.isReduced_of_presheaf_map_leTop_injective`: `B` is reduced.
* `TauCeti.AlgebraicGeometry.Spec.isDomain_and_isIntegrallyClosed_localization_atPrime_of_isEtaleAt`
  (the étale form): a finite torsion-free algebra over an integrally closed domain, étale
  at the points of `W`, is normal.

## References

* [The Stacks Project, Lemma 58.20.3](https://stacks.math.columbia.edu/tag/0BM9).
-/

public section

universe u

open CategoryTheory Opposite TopologicalSpace
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.StructureSheaf
open scoped nonZeroDivisors

namespace TauCeti.AlgebraicGeometry.Spec

variable {B : Type u} [CommRing B] {T : Submonoid B} {E : Type*} [CommRing E] [Algebra B E]
  [IsLocalization T E]

/-- Two solutions `b / u` of the equation `t z = x` near a prime `q`, in the sense of
`TauCeti.IsLocalization.exists_mul_eq_mul_of_isIntegral_mk'`, agree in `B_q`, because `t` is a
nonzerodivisor. -/
private theorem mul_mul_eq_of_mul_eq_mul {t x b₁ u₁ w₁ b₂ u₂ w₂ : B} (ht : t ∈ B⁰)
    (h₁ : w₁ * (b₁ * t) = w₁ * (u₁ * x)) (h₂ : w₂ * (b₂ * t) = w₂ * (u₂ * x)) :
    w₁ * w₂ * (b₁ * u₂) = w₁ * w₂ * (b₂ * u₁) := by
  rw [← sub_eq_zero]
  refine mem_nonZeroDivisors_iff_right.mp ht _ ?_
  linear_combination (u₂ * w₂) * h₁ - (u₁ * w₁) * h₂

/-- The form of `isIntegrallyClosedIn_of_presheaf_map_leTop_bijective` for the structure sheaf of
`Spec B` viewed on the topological space `PrimeSpectrum B`. -/
private theorem isIntegrallyClosedIn_of_toOpenₗ_bijective (hT : T ≤ B⁰)
    (U : Opens (PrimeSpectrum.Top B))
    (hU : ∀ p : PrimeSpectrum B, p ∈ U → IsDomain (Localization.AtPrime p.asIdeal) ∧
      IsIntegrallyClosed (Localization.AtPrime p.asIdeal))
    (hbij : Function.Bijective (toOpenₗ B B U)) :
    IsIntegrallyClosedIn B E := by
  refine isIntegrallyClosedIn_iff.mpr ⟨IsLocalization.injective E hT, fun {e} he ↦ ?_⟩
  obtain ⟨⟨x, t⟩, rfl⟩ := IsLocalization.mk'_surjective T e
  -- At each point `q` of `U`, `x / t` is a fraction `b q / u q` of `B_q`.
  have key (q : U) : ∃ b u w : B, u ∉ q.1.asIdeal ∧ w ∉ q.1.asIdeal ∧
      w * (b * t) = w * (u * x) := by
    obtain ⟨_, _⟩ := hU q.1 q.2
    exact IsLocalization.exists_mul_eq_mul_of_isIntegral_mk' hT x t he q.1.asIdeal
  choose b u w hu hw hbu using key
  -- These fractions glue to a section of `Spec B` over `U`.
  let s : (structureSheafInType B B).1.obj (op U) :=
    ⟨fun q ↦ LocalizedModule.mk (b q) ⟨u q, hu q⟩, fun q₀ ↦ by
      let V := U ⊓ PrimeSpectrum.basicOpen (u q₀ * w q₀)
      let i : V ⟶ U := homOfLE inf_le_left
      refine ⟨V, ⟨q₀.2, q₀.1.isPrime.mul_notMem (hu q₀) (hw q₀)⟩, i, b q₀, u q₀, fun q ↦ ?_⟩
      have hq : u q₀ * w q₀ ∉ (i q).1.asIdeal := q.2.2
      have h₀ : u q₀ ∉ (i q).1.asIdeal := fun h ↦ hq (Ideal.mul_mem_right _ _ h)
      have h₀' : w q₀ ∉ (i q).1.asIdeal := fun h ↦ hq (Ideal.mul_mem_left _ _ h)
      refine ⟨h₀, LocalizedModule.mk_eq.mpr
        ⟨⟨w (i q) * w q₀, (i q).1.isPrime.mul_notMem (hw (i q)) h₀'⟩, ?_⟩⟩
      simp only [Submonoid.smul_def, smul_eq_mul]
      linear_combination mul_mul_eq_of_mul_eq_mul (hT t.2) (hbu (i q)) (hbu q₀)⟩
  obtain ⟨c, hc⟩ := hbij.2 s
  refine ⟨c, (IsLocalization.eq_mk'_iff_mul_eq).mpr ?_⟩
  rw [← map_mul]
  -- The element `c t - x` vanishes at every point of `U`, hence is zero.
  suffices c * t = x by rw [this]
  rw [← sub_eq_zero]
  refine hbij.1 (((toOpenₗ B B U).map_zero).symm ▸ Subtype.ext (funext fun q ↦ ?_))
  have hcq := congrArg (fun r ↦ r.1 q) hc
  -- Evaluated at `q`, the two sections are the fractions `c / 1` and `b q / u q`.
  rw [toOpenₗ_eq_const] at hcq
  dsimp only [s] at hcq
  obtain ⟨v, hv⟩ := LocalizedModule.mk_eq.mp ((const_apply _ _ _ _ _).symm.trans hcq)
  simp only [Submonoid.smul_def, smul_eq_mul, one_mul] at hv
  -- `toOpenₗ` sends `c t - x` to the family of fractions `(c t - x) / 1`.
  rw [toOpenₗ_eq_const]
  refine (const_apply _ _ _ _ _).trans ?_
  refine (LocalizedModule.mk_eq.mpr ⟨⟨v * w q * u q, ?_⟩, ?_⟩).trans (LocalizedModule.zero_mk 1)
  · exact q.1.isPrime.mul_notMem (q.1.isPrime.mul_notMem v.2 (hw q)) (hu q)
  simp only [Submonoid.smul_def, OneMemClass.coe_one, smul_eq_mul, one_mul, mul_zero]
  linear_combination (w q * t) * hv + v * hbu q

/-- Let `W` be an open subset of `Spec B` such that restriction of sections of `Spec B` to `W` is
bijective and `B_q` is an integrally closed domain at every point `q` of `W`. Then `B` is
integrally closed in every localization of `B` at a submonoid of nonzerodivisors. -/
theorem isIntegrallyClosedIn_of_presheaf_map_leTop_bijective (hT : T ≤ B⁰)
    (W : (Spec (.of B)).Opens)
    (hW : ∀ p : PrimeSpectrum B, p ∈ W → IsDomain (Localization.AtPrime p.asIdeal) ∧
      IsIntegrallyClosed (Localization.AtPrime p.asIdeal))
    (hbij : Function.Bijective ((Spec (.of B)).presheaf.map W.leTop.op)) :
    IsIntegrallyClosedIn B E :=
  isIntegrallyClosedIn_of_toOpenₗ_bijective hT W hW
    ((Spec.presheaf_map_leTop_bijective_iff W).mp hbij)

/-- Let `W` be an open subset of `Spec B` such that restriction of sections of `Spec B` to `W` is
injective and `B_q` is reduced at every point `q` of `W`. Then `B` is reduced. -/
theorem isReduced_of_presheaf_map_leTop_injective (W : (Spec (.of B)).Opens)
    (hW : ∀ p : PrimeSpectrum B, p ∈ W → IsReduced (Localization.AtPrime p.asIdeal))
    (hinj : Function.Injective ((Spec (.of B)).presheaf.map W.leTop.op)) : IsReduced B := by
  -- The map `B → 𝒪(W)` is restriction precomposed with the isomorphism `B ≅ 𝒪(Spec B)`.
  have hinj' : Function.Injective (toOpenₗ B B (W : Opens (PrimeSpectrum.Top B))) :=
    hinj.comp (toOpenₗ_top_bijective (R := B) (M := B)).1
  refine ⟨fun b hb ↦ hinj' (((toOpenₗ B B W).map_zero).symm ▸
    Subtype.ext (funext fun q ↦ ?_))⟩
  have := hW q.1 q.2
  obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff q.1.asIdeal.primeCompl _ _).mp
    (hb.map (algebraMap B (Localization.AtPrime q.1.asIdeal))).eq_zero
  -- `toOpenₗ` sends `b` to the family of fractions `b / 1`.
  refine (congrArg (·.1 q) (toOpenₗ_eq_const _ b)).trans ((const_apply _ _ _ _ _).trans ?_)
  exact (LocalizedModule.mk_eq.mpr ⟨c, by simp [Submonoid.smul_def, hc]⟩).trans
    (LocalizedModule.zero_mk 1)

/-- Let `W` be an open subset of `Spec B` such that restriction of sections of `Spec B` to `W` is
bijective and `B_q` is an integrally closed domain at every point `q` of `W`. Then `B` is
integrally closed in its total ring of fractions. -/
theorem isIntegrallyClosed_of_presheaf_map_leTop_bijective (W : (Spec (.of B)).Opens)
    (hW : ∀ p : PrimeSpectrum B, p ∈ W → IsDomain (Localization.AtPrime p.asIdeal) ∧
      IsIntegrallyClosed (Localization.AtPrime p.asIdeal))
    (hbij : Function.Bijective ((Spec (.of B)).presheaf.map W.leTop.op)) :
    IsIntegrallyClosed B :=
  (isIntegrallyClosed_iff_isIntegrallyClosedIn (FractionRing B)).mpr
    (isIntegrallyClosedIn_of_presheaf_map_leTop_bijective le_rfl W hW hbij)

open scoped TensorProduct in
/-- Let `A` be an integrally closed domain and `B` a finite, finitely presented, torsion-free
`A`-algebra. Let `W` be an open subset of `Spec B` at whose points `B` is étale over `A`, and such
that restriction of sections of `Spec B` to `W` is bijective. Then every localization of `B` at a
prime is an integrally closed domain. -/
theorem isDomain_and_isIntegrallyClosed_localization_atPrime_of_isEtaleAt {A : Type*}
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra A B] [Module.Finite A B]
    [Algebra.FinitePresentation A B] [Module.IsTorsionFree A B] (W : (Spec (.of B)).Opens)
    (het : ∀ p : PrimeSpectrum B, p ∈ W → Algebra.IsEtaleAt A p.asIdeal)
    (hbij : Function.Bijective ((Spec (.of B)).presheaf.map W.leTop.op)) (q : Ideal B)
    [q.IsPrime] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  -- At the points of `W`, `B` is étale over the integrally closed domain `A`, hence normal.
  have hW (p : PrimeSpectrum B) (hp : p ∈ W) : IsDomain (Localization.AtPrime p.asIdeal) ∧
      IsIntegrallyClosed (Localization.AtPrime p.asIdeal) := by
    have := het p hp
    have := isIntegrallyClosed_of_isLocalization (Localization.AtPrime (p.asIdeal.under A))
      _ (p.asIdeal.under A).primeCompl_le_nonZeroDivisors
    exact ⟨TauCeti.Algebra.IsEtaleAt.isDomain_localization_atPrime_of_localization_under A _,
      TauCeti.Algebra.IsEtaleAt.isIntegrallyClosed_localization_atPrime_of_localization_under A _⟩
  -- The generic fibre `E` of `B` is a reduced Artinian localization of `B` at nonzerodivisors.
  let K := FractionRing A
  let E := K ⊗[A] B
  let : Algebra B E := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) E :=
    IsLocalization.tensorRight (S := B) K A⁰
  have hT : Algebra.algebraMapSubmonoid B A⁰ ≤ B⁰ := by
    rintro _ ⟨a, ha, rfl⟩
    exact mem_nonZeroDivisors_iff_right.mpr fun b hb ↦
      (Module.IsTorsionFree.isSMulRegular (isRegular_iff_mem_nonZeroDivisors.mpr ha))
        (by simpa [Algebra.smul_def, mul_comm] using hb)
  have : IsArtinianRing E := IsArtinianRing.of_finite K E
  have : IsReduced B := isReduced_of_presheaf_map_leTop_injective W
    (fun p hp ↦ have := (hW p hp).1; inferInstance) hbij.1
  have : IsReduced E := isReduced_of_injective
    (IsLocalization.algEquiv (Algebra.algebraMapSubmonoid B A⁰) E
      (Localization (Algebra.algebraMapSubmonoid B A⁰))).toRingHom
    (IsLocalization.algEquiv _ _ _).injective
  -- `B` is integrally closed in `E`, so it is normal.
  have := isIntegrallyClosedIn_of_presheaf_map_leTop_bijective (E := E) hT W hW hbij
  exact ⟨IsIntegrallyClosedIn.isDomain_localization_atPrime E q,
    IsIntegrallyClosedIn.isIntegrallyClosed_localization_atPrime E q⟩

end TauCeti.AlgebraicGeometry.Spec
