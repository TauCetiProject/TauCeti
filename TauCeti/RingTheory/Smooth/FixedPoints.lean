/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Smooth.Basic
public import TauCeti.RingTheory.Invariant.FixedPointIdeal
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Smoothness of fixed-point schemes under finite groups of invertible order

Let `G` be a finite group acting on a commutative `R`-algebra `A` by `R`-algebra automorphisms, and
assume that `(Nat.card G : R)` is a unit in `R`. Edixhoven's fixed-point theorem
(`formallySmooth_quotient_fixedPointIdeal`, `smooth_quotient_fixedPointIdeal`) states that if `A` is
formally smooth (respectively smooth) over `R`, then the fixed-point quotient
`A ⧸ fixedPointIdeal G A` — the coordinate ring of the closed subscheme `(Spec A)ᴳ` of `G`-fixed
points — is formally smooth (respectively smooth) over `R`. No Noetherian, Dedekind, or Henselian
assumption on `R` is required.

The proof uses the infinitesimal lifting criterion. Given a commutative `R`-algebra `B`, a
square-zero ideal `J` of `B`, and an `R`-algebra homomorphism
`f : (A ⧸ fixedPointIdeal G A) →ₐ[R] B ⧸ J`, formal smoothness of `A` supplies an `R`-algebra lift
`l₀ : A →ₐ[R] B` of `f ∘ mk`. Because `f ∘ mk` is `G`-invariant, every displacement
`d_g(a) = l₀(g • a) - l₀(a)` lies in `J`. Since `J ^ 2 = ⊥`, products `d_g(a) * d_h(b)` vanish in
`B`, which forces the Reynolds average

```text
l(a) = |G|⁻¹ • ∑ g : G, l₀(g • a) = l₀(a) + |G|⁻¹ • ∑ g : G, d_g(a)
```

to be multiplicative as well as `R`-linear (`averagedLiftAlgHom`). By reindexing the sum over `G`,
`l` is `G`-invariant and coincides with `l₀` modulo `J`, so it descends to
`(A ⧸ fixedPointIdeal G A) →ₐ[R] B` lifting `f`.

For formally étale (and étale) algebras, no group structure or invertibility of `|G|` is needed:
formal unramifiedness makes the infinitesimal lift `l₀ : A →ₐ[R] B` unique, hence automatically
invariant under any monoid `M` acting by `R`-algebra endomorphisms
(`formallyEtale_quotient_fixedPointIdeal`, `etale_quotient_fixedPointIdeal`).

## Main results

* `TauCeti.MulSemiringAction.formallySmooth_quotient_fixedPointIdeal`: if `A` is formally smooth
  over `R` and `G` is a finite group with `IsUnit (Nat.card G : R)`, then
  `A ⧸ fixedPointIdeal G A` is formally smooth over `R`.
* `TauCeti.MulSemiringAction.smooth_quotient_fixedPointIdeal`: under the same hypotheses on `G`,
  if `A` is smooth over `R`, then `A ⧸ fixedPointIdeal G A` is smooth over `R`.
* `TauCeti.MulSemiringAction.formallyEtale_quotient_fixedPointIdeal`: for any monoid `M` acting by
  `R`-algebra endomorphisms on a formally étale `R`-algebra `A`, `A ⧸ fixedPointIdeal M A` is
  formally étale over `R`.
* `TauCeti.MulSemiringAction.etale_quotient_fixedPointIdeal`: if `M` is finite and `A` is étale
  over `R`, then `A ⧸ fixedPointIdeal M A` is étale over `R`.

## References

* B. Edixhoven, *Néron models and tame ramification*, Compositio Math. 81 (1992), Proposition 3.4,
  pp. 294–295.
-/

public section

namespace TauCeti.MulSemiringAction

section TameSmooth

variable {R G A : Type*} [CommRing R] [Group G] [CommRing A] [Algebra R A]
  [MulSemiringAction G A] [SMulCommClass G R A]

section AveragedLift

variable {B : Type*} [CommRing B] [Algebra R B]

omit [SMulCommClass G R A] in
/-- Multiplicativity of the infinitesimal Reynolds average modulo a square-zero ideal `J ^ 2 = ⊥`:
products of displacements `(l₀ (g • a) - l₀ a) * (l₀ (h • b) - l₀ b)` vanish in `B`. -/
private theorem averagedLift_map_mul [Fintype G] {J : Ideal B} (hJ : J ^ 2 = ⊥)
    (l₀ : A →ₐ[R] B) (hl₀ : ∀ (g : G) (a : A), l₀ (g • a) - l₀ a ∈ J) (c : R) (a b : A) :
    l₀ (a * b) + c • ∑ g : G, (l₀ (g • (a * b)) - l₀ (a * b)) =
      (l₀ a + c • ∑ g : G, (l₀ (g • a) - l₀ a)) *
        (l₀ b + c • ∑ h : G, (l₀ (h • b) - l₀ b)) := by
  have hprod_zero (g h : G) : (l₀ (g • a) - l₀ a) * (l₀ (h • b) - l₀ b) = 0 := by
    have hmem : (l₀ (g • a) - l₀ a) * (l₀ (h • b) - l₀ b) ∈ J ^ 2 := by
      rw [sq]
      exact Ideal.mul_mem_mul (hl₀ g a) (hl₀ h b)
    rwa [hJ, Ideal.mem_bot] at hmem
  have hd_mul (g : G) :
      l₀ (g • (a * b)) - l₀ (a * b) =
        l₀ a * (l₀ (g • b) - l₀ b) + (l₀ (g • a) - l₀ a) * l₀ b := by
    calc
      l₀ (g • (a * b)) - l₀ (a * b)
          = l₀ (g • a) * l₀ (g • b) - l₀ a * l₀ b := by rw [smul_mul', map_mul, map_mul]
      _ = l₀ a * (l₀ (g • b) - l₀ b) + (l₀ (g • a) - l₀ a) * l₀ b +
            (l₀ (g • a) - l₀ a) * (l₀ (g • b) - l₀ b) := by ring
      _ = l₀ a * (l₀ (g • b) - l₀ b) + (l₀ (g • a) - l₀ a) * l₀ b := by
            rw [hprod_zero g g, add_zero]
  have hcross :
      (c • ∑ g : G, (l₀ (g • a) - l₀ a)) * (c • ∑ h : G, (l₀ (h • b) - l₀ b)) = 0 := by
    have hmem : (c • ∑ g : G, (l₀ (g • a) - l₀ a)) *
        (c • ∑ h : G, (l₀ (h • b) - l₀ b)) ∈ J ^ 2 := by
      rw [sq, Algebra.smul_def, Algebra.smul_def]
      exact Ideal.mul_mem_mul
        (J.mul_mem_left _ (sum_mem fun g _ ↦ hl₀ g a))
        (J.mul_mem_left _ (sum_mem fun h _ ↦ hl₀ h b))
    rwa [hJ, Ideal.mem_bot] at hmem
  calc
    (l₀ (a * b) + c • ∑ g : G, (l₀ (g • (a * b)) - l₀ (a * b)))
        = l₀ a * l₀ b + c • ∑ g : G,
            (l₀ a * (l₀ (g • b) - l₀ b) + (l₀ (g • a) - l₀ a) * l₀ b) := by
          simp_rw [hd_mul]
          rw [map_mul]
    _ = l₀ a * l₀ b + l₀ a * (c • ∑ g : G, (l₀ (g • b) - l₀ b)) +
          (c • ∑ g : G, (l₀ (g • a) - l₀ a)) * l₀ b := by
          rw [Finset.sum_add_distrib, smul_add, ← Finset.mul_sum, ← Finset.sum_mul,
            mul_smul_comm, Algebra.smul_mul_assoc, add_assoc]
    _ = (l₀ a + c • ∑ g : G, (l₀ (g • a) - l₀ a)) *
          (l₀ b + c • ∑ h : G, (l₀ (h • b) - l₀ b)) := by
          rw [add_mul, mul_add, mul_add, hcross, add_zero]

/-- Let `G` be a finite group, let `J` be a square-zero ideal of `B`, and let `l₀ : A →ₐ[R] B` be an
`R`-algebra map whose displacements `l₀ (g • a) - l₀ a` all lie in `J`. For any `c : R`,
`a ↦ l₀ a + c • ∑ g : G, (l₀ (g • a) - l₀ a)` is an `R`-algebra homomorphism `A →ₐ[R] B`. -/
private noncomputable def averagedLiftAlgHom [Fintype G] {J : Ideal B} (hJ : J ^ 2 = ⊥)
    (l₀ : A →ₐ[R] B) (hl₀ : ∀ (g : G) (a : A), l₀ (g • a) - l₀ a ∈ J) (c : R) :
    A →ₐ[R] B where
  toFun a := l₀ a + c • ∑ g : G, (l₀ (g • a) - l₀ a)
  map_one' := by simp
  map_mul' := averagedLift_map_mul hJ l₀ hl₀ c
  map_zero' := by simp
  map_add' a b := by
    have hsum :
        (∑ g : G, (l₀ (g • (a + b)) - l₀ (a + b))) =
          (∑ g : G, (l₀ (g • a) - l₀ a)) + ∑ g : G, (l₀ (g • b) - l₀ b) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun g _ ↦ ?_
      simp only [smul_add, map_add]
      abel
    rw [hsum, map_add, smul_add]
    abel
  commutes' r := by simp [smul_algebraMap]

/-- When `c * (Fintype.card G : R) = 1`, `averagedLiftAlgHom` equals the normalized orbit sum
`a ↦ c • ∑ g : G, l₀ (g • a)`, hence is `G`-invariant and reduces to `l₀` modulo `J`. -/
private theorem averagedLiftAlgHom_eq_sum [Fintype G] {J : Ideal B} (hJ : J ^ 2 = ⊥)
    (l₀ : A →ₐ[R] B) (hl₀ : ∀ (g : G) (a : A), l₀ (g • a) - l₀ a ∈ J)
    {c : R} (hc : c * (Fintype.card G : R) = 1) (a : A) :
    averagedLiftAlgHom hJ l₀ hl₀ c a = c • ∑ g : G, l₀ (g • a) := by
  change l₀ a + c • ∑ g : G, (l₀ (g • a) - l₀ a) = c • ∑ g : G, l₀ (g • a)
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, smul_sub,
    ← Nat.cast_smul_eq_nsmul R, smul_smul, hc, one_smul]
  abel

end AveragedLift

/-- **Edixhoven's formal smoothness theorem (Proposition 3.4).** Let `G` be a finite group acting on
a formally smooth `R`-algebra `A` by `R`-algebra automorphisms. If `(Nat.card G : R)` is invertible
in `R`, then the fixed-point quotient `A ⧸ fixedPointIdeal G A` is formally smooth over `R`. -/
theorem formallySmooth_quotient_fixedPointIdeal [Finite G] [Algebra.FormallySmooth R A]
    (hG : IsUnit (Nat.card G : R)) :
    Algebra.FormallySmooth R (A ⧸ fixedPointIdeal G A) := by
  have := Fintype.ofFinite G
  set I := fixedPointIdeal G A
  refine Algebra.FormallySmooth.iff_comp_surjective.mpr fun B _ _ J hJ fbar ↦ ?_
  obtain ⟨l₀, hl₀⟩ :=
    Algebra.FormallySmooth.comp_surjective R A J hJ (fbar.comp (Ideal.Quotient.mkₐ R I))
  have hdisp (g : G) (a : A) : l₀ (g • a) - l₀ a ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
    have hga := congr($hl₀ (g • a))
    have ha := congr($hl₀ a)
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at hga ha
    rw [hga, ha, mk_smul_eq]
  let c : R := ↑hG.unit⁻¹
  have hc : c * (Fintype.card G : R) = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact Units.inv_mul_eq_one.mpr rfl
  let l : A →ₐ[R] B := averagedLiftAlgHom hJ l₀ hdisp c
  have hinv (h : G) (a : A) : l (h • a) = l a := by
    rw [averagedLiftAlgHom_eq_sum hJ l₀ hdisp hc, averagedLiftAlgHom_eq_sum hJ l₀ hdisp hc]
    congr 1
    exact Fintype.sum_equiv (Equiv.mulRight h) _ _ fun g ↦ by simp [mul_smul]
  refine ⟨(quotientFixedPointIdealAlgHomEquiv R G A B).symm ⟨l, hinv⟩, ?_⟩
  ext x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hsumJ : c • ∑ g : G, (l₀ (g • a) - l₀ a) ∈ J := by
    rw [Algebra.smul_def]
    exact J.mul_mem_left _ (sum_mem fun g _ ↦ hdisp g a)
  calc
    Ideal.Quotient.mkₐ R J (((quotientFixedPointIdealAlgHomEquiv R G A B).symm ⟨l, hinv⟩)
        (Ideal.Quotient.mk I a))
        = Ideal.Quotient.mk J (l₀ a + c • ∑ g : G, (l₀ (g • a) - l₀ a)) := by
          rw [quotientFixedPointIdealAlgHomEquiv_symm_apply_mk]
          rfl
    _ = Ideal.Quotient.mk J (l₀ a) := by
          rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hsumJ, add_zero]
    _ = fbar (Ideal.Quotient.mk I a) := congr($hl₀ a)

/-- **Edixhoven's smoothness theorem (Proposition 3.4).** Let `G` be a finite group acting on a
smooth `R`-algebra `A` by `R`-algebra automorphisms. If `(Nat.card G : R)` is invertible in `R`,
then the fixed-point quotient `A ⧸ fixedPointIdeal G A` is smooth over `R`. -/
theorem smooth_quotient_fixedPointIdeal [Finite G] [Algebra.Smooth R A]
    (hG : IsUnit (Nat.card G : R)) :
    Algebra.Smooth R (A ⧸ fixedPointIdeal G A) where
  formallySmooth := formallySmooth_quotient_fixedPointIdeal hG
  finitePresentation := finitePresentation_quotient_fixedPointIdeal

end TameSmooth

section Etale

variable {R M A : Type*} [CommRing R] [Monoid M] [CommRing A] [Algebra R A]
  [MulSemiringAction M A] [SMulCommClass M R A]

/-- For any monoid `M` acting by `R`-algebra endomorphisms on a formally étale `R`-algebra `A`,
the fixed-point quotient `A ⧸ fixedPointIdeal M A` is formally étale over `R`, with no finiteness
or invertibility assumption on `M`. -/
theorem formallyEtale_quotient_fixedPointIdeal [Algebra.FormallyEtale R A] :
    Algebra.FormallyEtale R (A ⧸ fixedPointIdeal M A) := by
  set I := fixedPointIdeal M A
  have : Algebra.FormallySmooth R (A ⧸ I) := by
    refine Algebra.FormallySmooth.iff_comp_surjective.mpr fun B _ _ J hJ fbar ↦ ?_
    obtain ⟨l, hl⟩ :=
      Algebra.FormallySmooth.comp_surjective R A J hJ (fbar.comp (Ideal.Quotient.mkₐ R I))
    have hinv (m : M) : l.comp (MulSemiringAction.toAlgHom R A m) = l := by
      apply Algebra.FormallyUnramified.comp_injective J hJ
      ext a
      have hm := congr($hl (m • a))
      have ha := congr($hl a)
      simp only [AlgHom.comp_apply, MulSemiringAction.toAlgHom_apply,
        Ideal.Quotient.mkₐ_eq_mk] at hm ha ⊢
      rw [hm, ha, mk_smul_eq]
    refine ⟨(quotientFixedPointIdealAlgHomEquiv R M A B).symm
      ⟨l, fun m a ↦ congr($(hinv m) a)⟩, ?_⟩
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [I, AlgHom.comp_apply, quotientFixedPointIdealAlgHomEquiv_symm_apply_mk]
    exact congr($hl a)
  exact Algebra.FormallyEtale.of_formallyUnramified_and_formallySmooth

/-- For any finite monoid `M` acting by `R`-algebra endomorphisms on an étale `R`-algebra `A`,
the fixed-point quotient `A ⧸ fixedPointIdeal M A` is étale over `R`. -/
theorem etale_quotient_fixedPointIdeal [Finite M] [Algebra.Etale R A] :
    Algebra.Etale R (A ⧸ fixedPointIdeal M A) where
  formallyEtale := formallyEtale_quotient_fixedPointIdeal
  finitePresentation := finitePresentation_quotient_fixedPointIdeal

end Etale

end TauCeti.MulSemiringAction
