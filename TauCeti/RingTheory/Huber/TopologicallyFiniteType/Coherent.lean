/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Coherent.Basic
public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Saturated

import Mathlib.RingTheory.Finiteness.Ideal
import TauCeti.Algebra.Module.Torsion.Basic

/-!
# Coherence of algebras topologically of finite presentation

Let `O` be a valuation domain carrying `TauCeti.Huber.IsCompleteRankOneBase O ϖ`, possibly
non-noetherian (such as `𝒪_{ℂ_p}`). Over a quotient `A` of a restricted power-series algebra
`O⟨ξ₁, …, ξₙ⟩`, every finite `A`-module without `ϖ`-torsion is finitely presented
(`TauCeti.Huber.finitePresentation_of_torsionBy_eq_bot_of_surjective`). This file draws the
ring-theoretic consequences of Bosch–Lütkebohmert I, §1, which make algebras topologically of
finite presentation behave like noetherian rings in the absence of noetherianity: they are the
coherent rings underlying coherent sheaves on admissible formal schemes, and being topologically
of finite presentation is a property of the algebra rather than of a chosen presentation.

## Main results

* `TauCeti.Huber.isCoherent_of_torsionBy_eq_bot_of_surjective`: over a quotient of `O⟨ξ⟩`, a
  finite module without `ϖ`-torsion is coherent.
* `TauCeti.Huber.isCoherentRing_restrictedMvPowerSeriesCompletion`: `O⟨ξ₁, …, ξₙ⟩` is a coherent
  ring.
* `TauCeti.Huber.IsTopologicallyFinitePresentation.isCoherentRing`: an algebra topologically of
  finite presentation is a coherent ring (Bosch–Lütkebohmert I, Proposition 1.3), that is, its
  finitely generated ideals are finitely presented
  (`TauCeti.Huber.IsTopologicallyFinitePresentation.finitePresentation_of_fg`).
* `TauCeti.Huber.isCoherent_primaryComponent_of_surjective`: the `ϖ`-power torsion of a coherent
  module over a quotient of `O⟨ξ⟩` is coherent (Bosch–Lütkebohmert I, Lemma 1.4(c)).
* `TauCeti.Huber.isAdmissibleAlgebra_of_torsionBy_eq_bot`: a quotient of `O⟨ξ⟩` without
  `ϖ`-torsion is admissible, and `TauCeti.Huber.isTopologicallyFinitePresentation_of_flat`: a flat
  `O`-algebra topologically of finite type is topologically of finite presentation
  (Bosch–Lütkebohmert I, Proposition 1.1(c)).
* `TauCeti.Huber.IsTopologicallyFinitePresentation.isAdmissibleAlgebra_quotient_primaryComponent`:
  the quotient of an algebra topologically of finite presentation by its `ϖ`-power torsion is
  admissible.
* `TauCeti.Huber.IsTopologicallyFinitePresentation.iff_of_surjective`: once `A` is topologically
  of finite presentation, every surjection `O⟨ξ⟩ → A` has finitely generated kernel.

## Implementation notes

The independence of the presentation is proved without lifting maps between restricted
power-series algebras. For a surjection `π : O⟨ξ⟩ → A` with kernel `𝔞`, let `𝔞'` be the preimage of
the `ϖ`-power torsion of `A`, which is `ϖ`-saturated and hence finitely generated, and let `ϖᵏ`
kill that torsion. Then `𝔞 = (𝔞 + ϖᵏ·O⟨ξ⟩) ∩ 𝔞'`. The first ideal is finitely generated because
`A ⧸ ϖᵏA` and `(O ⧸ ϖᵏ)[ξ]` are finitely presented `O ⧸ ϖᵏ`-algebras, and the intersection of two
finitely generated ideals of the coherent ring `O⟨ξ⟩` is finitely generated.

## References

* S. Bosch and W. Lütkebohmert, *Formal and rigid geometry. I. Rigid spaces*, Math. Ann. 295
  (1993), §1, Proposition 1.1(c), Proposition 1.3 and Lemma 1.4(c).
* K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*, Ch. 0, §8.5 and Ch. I, §2.3,
  Corollary 2.3.2.
-/

public section

namespace TauCeti.Huber

universe u

variable {O : Type u} [CommRing O] [IsDomain O] [ValuationRing O] [TopologicalSpace O]
  [NonarchimedeanRing O] (ϖ : O) [IsCompleteRankOneBase O ϖ]

/-! ### Coherence -/

include ϖ in
/-- **Finite `ϖ`-torsion-free modules are coherent.** Over a quotient `A` of `O⟨ξ₁, …, ξₙ⟩`, a
finite `A`-module `E` without `ϖ`-torsion is coherent: its finitely generated submodules are again
finite and `ϖ`-torsion-free, hence finitely presented. -/
theorem isCoherent_of_torsionBy_eq_bot_of_surjective {A E : Type*} [CommRing A] [Algebra O A]
    [AddCommGroup E] [Module A E] [Module O E] [IsScalarTower O A E] [Module.Finite A E]
    {n : ℕ} {π : restrictedMvPowerSeriesCompletion n O →ₐ[O] A} (hπ : Function.Surjective π)
    (htors : Submodule.torsionBy O E ϖ = ⊥) :
    Module.IsCoherent A E where
  finitePresentation_of_fg N hN := by
    have : Module.Finite A N := Module.Finite.iff_fg.mpr hN
    refine finitePresentation_of_torsionBy_eq_bot_of_surjective ϖ hπ (eq_bot_iff.mpr fun x hx ↦ ?_)
    have hx' : (x : E) ∈ Submodule.torsionBy O E ϖ := by
      rw [Submodule.mem_torsionBy_iff] at hx ⊢
      exact congrArg Subtype.val hx
    rw [htors, Submodule.mem_bot] at hx'
    exact (Submodule.mem_bot _).mpr (Subtype.ext hx')

include ϖ in
/-- **Restricted power series over a complete rank-one valuation ring form a coherent ring**:
every finitely generated ideal of `O⟨ξ₁, …, ξₙ⟩` is finitely presented, although `O⟨ξ₁, …, ξₙ⟩`
is noetherian only when `O` is. -/
theorem isCoherentRing_restrictedMvPowerSeriesCompletion (n : ℕ) :
    IsCoherentRing (restrictedMvPowerSeriesCompletion n O) := by
  have : IsAdicRing O := IsCompleteRankOneBase.isAdicRing ϖ
  have hϖ : IsSMulRegular O ϖ := .of_ne_zero (IsCompleteRankOneBase.ne_zero (ϖ := ϖ))
  exact isCoherent_of_torsionBy_eq_bot_of_surjective ϖ (π := AlgHom.id O _)
    Function.surjective_id
    (isAdmissibleAlgebra_restrictedMvPowerSeriesCompletion O hϖ n).torsionBy_eq_bot

variable {A : Type*} [CommRing A] [Algebra O A]

include ϖ in
/-- **Algebras topologically of finite presentation are coherent rings** (Bosch–Lütkebohmert I,
§1, Proposition 1.3). Consequently every finitely presented module over such an algebra is
coherent (`TauCeti.IsCoherentRing.isCoherent_of_finitePresentation`), and kernels, cokernels,
intersections, tensor products and annihilators of coherent modules are coherent. -/
theorem IsTopologicallyFinitePresentation.isCoherentRing
    (hA : IsTopologicallyFinitePresentation O A) : IsCoherentRing A := by
  obtain ⟨n, π, hπ, hker⟩ := (isTopologicallyFinitePresentation_iff O A).mp hA
  have := isCoherentRing_restrictedMvPowerSeriesCompletion ϖ n
  exact (Ideal.quotientKerAlgEquivOfSurjective hπ).toRingEquiv.isCoherentRing_iff.mp
    (IsCoherentRing.quotient hker)

include ϖ in
/-- Every finitely generated ideal of an algebra topologically of finite presentation is finitely
presented (Bosch–Lütkebohmert I, §1, Proposition 1.3). -/
theorem IsTopologicallyFinitePresentation.finitePresentation_of_fg
    (hA : IsTopologicallyFinitePresentation O A) (J : Ideal A) (hJ : J.FG) :
    Module.FinitePresentation A J :=
  (hA.isCoherentRing ϖ).finitePresentation_of_fg hJ

include ϖ in
/-- **The `ϖ`-power torsion of a coherent module is coherent** (Bosch–Lütkebohmert I, §1,
Lemma 1.4(c)). Over a quotient `A` of `O⟨ξ₁, …, ξₙ⟩`, the `(ϖ)`-primary torsion submodule
`E[ϖ^∞]` of a coherent `A`-module `E` is coherent. -/
theorem isCoherent_primaryComponent_of_surjective {E : Type*} [AddCommGroup E] [Module A E]
    [Module.IsCoherent A E] {n : ℕ} {π : restrictedMvPowerSeriesCompletion n O →ₐ[O] A}
    (hπ : Function.Surjective π) :
    Module.IsCoherent A ((Ideal.span {algebraMap O A ϖ}).primaryComponent E) :=
  Module.IsCoherent.of_fg_submodule (fg_primaryComponent_of_surjective ϖ hπ)

include ϖ in
/-- The `ϖ`-power torsion of a coherent module over an algebra topologically of finite
presentation is coherent (Bosch–Lütkebohmert I, §1, Lemma 1.4(c)). -/
theorem IsTopologicallyFinitePresentation.isCoherent_primaryComponent {E : Type*}
    [AddCommGroup E] [Module A E] [Module.IsCoherent A E]
    (hA : IsTopologicallyFinitePresentation O A) :
    Module.IsCoherent A ((Ideal.span {algebraMap O A ϖ}).primaryComponent E) :=
  Module.IsCoherent.of_fg_submodule (hA.fg_primaryComponent ϖ)

/-! ### Torsion-free quotients are admissible -/

include ϖ in
/-- **A `ϖ`-torsion-free algebra topologically of finite type is admissible**
(Bosch–Lütkebohmert I, §1, Proposition 1.1(c)). If `π : O⟨ξ₁, …, ξₙ⟩ → A` is surjective and `A`
has no `ϖ`-torsion, then `ker π` is `ϖ`-saturated, hence finitely generated, so `A` is
topologically of finite presentation and admissible. -/
theorem isAdmissibleAlgebra_of_torsionBy_eq_bot {n : ℕ}
    (π : restrictedMvPowerSeriesCompletion n O →ₐ[O] A) (hπ : Function.Surjective π)
    (htors : Submodule.torsionBy O A ϖ = ⊥) :
    IsAdmissibleAlgebra ϖ A := by
  refine ⟨(isTopologicallyFinitePresentation_iff O A).mpr ⟨n, π, hπ, ?_⟩, htors⟩
  refine fg_of_forall_smul_mem_of_surjective ϖ (π := AlgHom.id O _) Function.surjective_id
    fun x hx ↦ ?_
  rw [RingHom.mem_ker] at hx ⊢
  have hπx : π x ∈ Submodule.torsionBy O A ϖ := by
    rw [Submodule.mem_torsionBy_iff, ← map_smul, hx]
  rw [htors, Submodule.mem_bot] at hπx
  exact hπx

include ϖ in
/-- **A flat `O`-algebra topologically of finite type is topologically of finite presentation**
(Bosch–Lütkebohmert I, §1, Proposition 1.1(c); Fujiwara–Kato, Ch. I, §2.3, Corollary 2.3.2). -/
theorem isTopologicallyFinitePresentation_of_flat [Module.Flat O A] {n : ℕ}
    (π : restrictedMvPowerSeriesCompletion n O →ₐ[O] A) (hπ : Function.Surjective π) :
    IsTopologicallyFinitePresentation O A :=
  have hϖ : IsSMulRegular A ϖ := Module.Flat.isSMulRegular_of_nonZeroDivisors <|
    mem_nonZeroDivisors_of_ne_zero (IsCompleteRankOneBase.ne_zero (ϖ := ϖ))
  (isAdmissibleAlgebra_of_torsionBy_eq_bot ϖ π hπ
    ((isSMulRegular_iff_torsionBy_eq_bot A ϖ).mp hϖ)).isTopologicallyFinitePresentation

include ϖ in
/-- **The torsion-free quotient is admissible.** If `A` is topologically of finite presentation,
then so is its quotient by the `ϖ`-power torsion ideal `A[ϖ^∞]`, which has no `ϖ`-torsion. It is
the `ϖ`-power torsion, not the `ϖ`-torsion, that has to be divided out: for
`A = O⟨T⟩ ⧸ (ϖ²T)` the quotient by `A[ϖ]` still has `ϖ`-torsion. -/
theorem IsTopologicallyFinitePresentation.isAdmissibleAlgebra_quotient_primaryComponent
    (hA : IsTopologicallyFinitePresentation O A) :
    IsAdmissibleAlgebra ϖ (A ⧸ (Ideal.span {algebraMap O A ϖ}).primaryComponent A) := by
  refine ⟨hA.quotient (hA.fg_primaryComponent ϖ), ?_⟩
  refine (Submodule.torsionBy_quotient_eq_bot_iff_forall_smul_mem _ ϖ).mpr fun x hx ↦ ?_
  exact (Ideal.smul_mem_primaryComponent_span_singleton_iff _).mp (by rwa [algebraMap_smul])

/-! ### Independence of the presentation -/

omit [IsDomain O] [ValuationRing O] in
include ϖ in
/-- For a surjection `π : O⟨ξ⟩ → A` onto an algebra topologically of finite presentation and every
`k`, the ideal `ker π + ϖᵏ·O⟨ξ⟩ = π⁻¹(ϖᵏA)` is finitely generated, because it is the kernel of a
surjection `(O ⧸ ϖᵏ)[ξ] → A ⧸ ϖᵏA` of finitely presented `O ⧸ ϖᵏ`-algebras. -/
private theorem fg_comap_span_pow_of_surjective (hA : IsTopologicallyFinitePresentation O A)
    {n : ℕ} (π : restrictedMvPowerSeriesCompletion n O →ₐ[O] A) (hπ : Function.Surjective π)
    (k : ℕ) :
    (Ideal.comap π ((Ideal.span {ϖ ^ k}).map (algebraMap O A))).FG := by
  set P := restrictedMvPowerSeriesCompletion n O
  set IP := (Ideal.span {ϖ ^ k}).map (algebraMap O P)
  set IA := (Ideal.span {ϖ ^ k}).map (algebraMap O A)
  have hϖ : IsAdic (Ideal.span {ϖ}) := IsCompleteRankOneBase.isAdic
  have hle : IP ≤ IA.comap π := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap, AlgHom.commutes]
    exact Ideal.mem_map_of_mem _ ha
  -- the reduction of `π` modulo `ϖᵏ`, as a map of `O ⧸ ϖᵏ`-algebras
  let g : P ⧸ IP →ₐ[O ⧸ Ideal.span {ϖ ^ k}] A ⧸ IA :=
    AlgHom.extendScalarsOfSurjective Ideal.Quotient.mk_surjective (Ideal.quotientMapₐ IA π hle)
  have hg : Function.Surjective g := Ideal.quotientMap_surjective (H := hle) hπ
  have : Algebra.FinitePresentation (O ⧸ Ideal.span {ϖ ^ k}) (P ⧸ IP) :=
    IsTopologicallyFinitePresentation.finitePresentation_quotient_pow
      (isTopologicallyFinitePresentation_restrictedMvPowerSeriesCompletion O n) hϖ k
  have : Algebra.FinitePresentation (O ⧸ Ideal.span {ϖ ^ k}) (A ⧸ IA) :=
    hA.finitePresentation_quotient_pow hϖ k
  have hcomp : IA.comap π = RingHom.ker (g.toRingHom.comp (Ideal.Quotient.mk IP)) := by
    have hgmk (x : P) : g (Ideal.Quotient.mk IP x) = Ideal.Quotient.mk IA (π x) := by
      rw [← AlgHom.restrictScalars_apply O, AlgHom.restrictScalars_extendScalarsOfSurjective,
        Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk]
    ext x
    simp only [Ideal.mem_comap, RingHom.mem_ker, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, hgmk, Ideal.Quotient.eq_zero_iff_mem]
  rw [hcomp]
  refine Ideal.fg_ker_comp _ _ ?_ (Algebra.FinitePresentation.ker_fG_of_surjective g hg)
    Ideal.Quotient.mk_surjective
  rw [Ideal.mk_ker]
  exact Ideal.FG.map ⟨{ϖ ^ k}, by simp⟩ _

include ϖ in
/-- **Topological finite presentation does not depend on the presentation** (Bosch–Lütkebohmert
I, §1, p. 293). Every surjection `π : O⟨ξ₁, …, ξₙ⟩ → A` onto an algebra topologically of finite
presentation has finitely generated kernel. -/
theorem IsTopologicallyFinitePresentation.iff_of_surjective {n : ℕ}
    (π : restrictedMvPowerSeriesCompletion n O →ₐ[O] A) (hπ : Function.Surjective π) :
    IsTopologicallyFinitePresentation O A ↔ (RingHom.ker π).FG := by
  refine ⟨fun hA ↦ ?_, fun hker ↦ (isTopologicallyFinitePresentation_iff O A).mpr ⟨n, π, hπ, hker⟩⟩
  set P := restrictedMvPowerSeriesCompletion n O
  set T := (Ideal.span {algebraMap O A ϖ}).primaryComponent A
  have := isCoherentRing_restrictedMvPowerSeriesCompletion ϖ n
  -- the preimage of the `ϖ`-power torsion is `ϖ`-saturated, hence finitely generated
  have hT : (Ideal.comap π T).FG := by
    refine fg_of_forall_smul_mem_of_surjective ϖ (π := AlgHom.id O P) Function.surjective_id
      fun x hx ↦ ?_
    rw [Ideal.mem_comap, map_smul] at hx
    exact (Ideal.smul_mem_primaryComponent_span_singleton_iff _).mp (by rwa [algebraMap_smul])
  -- a single power `ϖᵏ` kills the `ϖ`-power torsion
  obtain ⟨k, hk⟩ := exists_pow_smul_eq_zero_primaryComponent_of_surjective (E := A) ϖ hπ
  set B := Ideal.comap π ((Ideal.span {ϖ ^ k}).map (algebraMap O A))
  have hB : B.FG := fg_comap_span_pow_of_surjective ϖ hA π hπ k
  -- `ker π = π⁻¹(ϖᵏA) ∩ π⁻¹(A[ϖ^∞])`
  have heq : RingHom.ker π = B ⊓ Ideal.comap π T := by
    refine le_antisymm (le_inf (fun x hx ↦ ?_) fun x hx ↦ ?_) fun x hx ↦ ?_
    · rw [RingHom.mem_ker] at hx
      simp [B, hx]
    · rw [RingHom.mem_ker] at hx
      simp [hx]
    · obtain ⟨hxB, hxT⟩ := Submodule.mem_inf.mp hx
      rw [Ideal.mem_comap] at hxB hxT
      rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hxB
      obtain ⟨y, hy⟩ := hxB
      have hy' : π x = algebraMap O A ϖ ^ k • y := by rw [← hy, smul_eq_mul, mul_comm, map_pow]
      have hyT : y ∈ T := by
        rwa [hy', Ideal.pow_smul_mem_primaryComponent_span_singleton_iff] at hxT
      rw [RingHom.mem_ker, hy', ← map_pow, algebraMap_smul, hk y hyT]
  have : Module.IsCoherent P B := (Submodule.isCoherent_iff_fg).mpr hB
  have : Module.IsCoherent P (Ideal.comap π T) := (Submodule.isCoherent_iff_fg).mpr hT
  rw [heq]
  exact Module.Finite.iff_fg.mp inferInstance

end TauCeti.Huber
