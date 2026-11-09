/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Flat.TorsionFree
public import TauCeti.RingTheory.Huber.CompleteRankOneBase
public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Basic

import TauCeti.RingTheory.Huber.Restricted.Adic
import TauCeti.RingTheory.Huber.Restricted.Reduction
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Complete

/-!
# Algebras topologically of finite presentation

Let `O` be a nonarchimedean ring, typically the valuation ring of a complete nonarchimedean field
with a nontrivial rank-one absolute value, carrying the `ϖ`-adic topology for a pseudouniformiser
`ϖ`. An `O`-algebra `A` is *topologically of finite presentation* if it is isomorphic to a
quotient `O⟨ξ₁, …, ξₙ⟩ ⧸ (f₁, …, fₘ)` of a restricted power-series algebra by a finitely
generated ideal, and *admissible* if moreover it has no `ϖ`-torsion. These are the rings of
functions on the affine pieces of the admissible formal schemes of Raynaud and
Bosch–Lütkebohmert, whose generic fibres are the affinoid rigid spaces.

The predicate is purely algebraic: `A` carries no topology, and the presentation map is only
required to be a surjective `O`-algebra homomorphism. When `A` does carry the `ϖ`-adic topology,
every presentation is automatically an open quotient map, so that `A` is strictly topologically
of finite type over `O` in the sense of `TauCeti.Huber.IsStrictlyTopologicallyFiniteType`
(`TauCeti.Huber.IsTopologicallyFinitePresentation.isStrictlyTopologicallyFiniteType`).

The word *admissible* is Bosch–Lütkebohmert's and is unrelated to EGA's admissible topological
rings. Over a valuation ring that is `ϖ`-adically separated, a module without `ϖ`-torsion has no
torsion at all, so that admissible algebras are exactly the flat algebras topologically of finite
presentation (`TauCeti.Huber.isAdmissibleAlgebra_iff_flat`).

## Main definitions

* `TauCeti.Huber.IsTopologicallyFinitePresentation`: `A` is a quotient of some `O⟨ξ₁, …, ξₙ⟩` by
  a finitely generated ideal.
* `TauCeti.Huber.IsAdmissibleAlgebra`: `A` is topologically of finite presentation and has no
  `ϖ`-torsion.

## Main results

* `TauCeti.Huber.IsTopologicallyFinitePresentation.of_surjective`: a quotient of an algebra
  topologically of finite presentation by a finitely generated ideal is again topologically of
  finite presentation; `TauCeti.Huber.IsTopologicallyFinitePresentation.quotient` and
  `TauCeti.Huber.IsTopologicallyFinitePresentation.of_algEquiv` are the two special cases.
* `TauCeti.Huber.isTopologicallyFinitePresentation_restrictedMvPowerSeriesCompletion`:
  `O⟨ξ₁, …, ξₙ⟩` itself is topologically of finite presentation, hence so is every
  `O⟨ξ⟩ ⧸ (f₁, …, fₘ)`; `TauCeti.Huber.isTopologicallyFinitePresentation_self` is the case of
  no variables over a complete adic ring.
* `TauCeti.Huber.isOpenQuotientMap_of_surjective_restrictedMvPowerSeriesCompletion` and
  `TauCeti.Huber.IsTopologicallyFinitePresentation.isStrictlyTopologicallyFiniteType`: for the
  adic topology on `A` of an ideal of definition of `O`, every presentation is an open quotient
  map, so `A` is strictly topologically of finite type over `O`.
* `TauCeti.Huber.IsTopologicallyFinitePresentation.finitePresentation_quotient`: for a finitely
  generated ideal of definition `I` of a complete adic ring `O`, the reduction `A ⧸ I·A` is a
  finitely presented `O ⧸ I`-algebra; in particular every `A ⧸ ϖᵐA` is finitely presented over
  `O ⧸ ϖᵐ` (`TauCeti.Huber.IsTopologicallyFinitePresentation.finitePresentation_quotient_pow`).
* `TauCeti.Huber.isAdmissibleAlgebra_iff_flat`: over a `ϖ`-adically separated valuation ring, an
  algebra is admissible exactly when it is topologically of finite presentation and flat.
* `TauCeti.Huber.isAdmissibleAlgebra_restrictedMvPowerSeriesCompletion`: over a complete adic
  domain, `O⟨ξ₁, …, ξₙ⟩` is admissible.

## References

* S. Bosch and W. Lütkebohmert, *Formal and rigid geometry. I. Rigid spaces*, Math. Ann. 295
  (1993), §1, the definitions preceding Proposition 1.1, p. 293.
* B. Conrad, *Several approaches to non-archimedean geometry*, in *p-adic Geometry* (Arizona
  Winter School 2007), §3.3, p. 30.
* K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*, Ch. 0, §8.4, Definition 8.4.1.
-/

public section

namespace TauCeti.Huber

section Definitions

variable (O : Type*) [CommRing O] [TopologicalSpace O] [NonarchimedeanRing O]
  (A : Type*) [CommRing A] [Algebra O A]

/-- An `O`-algebra `A` is **topologically of finite presentation** if it is a quotient of a
restricted power-series algebra `O⟨ξ₁, …, ξₙ⟩` in finitely many variables by a finitely generated
ideal: there is a surjective `O`-algebra homomorphism `O⟨ξ₁, …, ξₙ⟩ → A` with finitely generated
kernel. No topology on `A` is involved (Bosch–Lütkebohmert I, §1). -/
def IsTopologicallyFinitePresentation : Prop :=
  ∃ (n : ℕ) (π : restrictedMvPowerSeriesCompletion n O →ₐ[O] A),
    Function.Surjective π ∧ (RingHom.ker π).FG

/-- Unfolding lemma for the sealed definition `TauCeti.Huber.IsTopologicallyFinitePresentation`. -/
theorem isTopologicallyFinitePresentation_iff :
    IsTopologicallyFinitePresentation O A ↔
      ∃ (n : ℕ) (π : restrictedMvPowerSeriesCompletion n O →ₐ[O] A),
        Function.Surjective π ∧ (RingHom.ker π).FG :=
  Iff.rfl

end Definitions

/-- An `O`-algebra `A` is **admissible** (in the sense of Bosch–Lütkebohmert, for the element
`ϖ` of `O`) if it is topologically of finite presentation and has no `ϖ`-torsion. -/
structure IsAdmissibleAlgebra {O : Type*} [CommRing O] [TopologicalSpace O] [NonarchimedeanRing O]
    (ϖ : O) (A : Type*) [CommRing A] [Algebra O A] : Prop where
  isTopologicallyFinitePresentation : IsTopologicallyFinitePresentation O A
  torsionBy_eq_bot : Submodule.torsionBy O A ϖ = ⊥

variable {O : Type*} [CommRing O] [TopologicalSpace O] [NonarchimedeanRing O]
  {A : Type*} [CommRing A] [Algebra O A] {B : Type*} [CommRing B] [Algebra O B]

/-! ### Stability properties -/

/-- A quotient of an algebra topologically of finite presentation by a finitely generated ideal
is topologically of finite presentation. -/
theorem IsTopologicallyFinitePresentation.of_surjective (hA : IsTopologicallyFinitePresentation O A)
    (f : A →ₐ[O] B) (hf : Function.Surjective f) (hker : (RingHom.ker f).FG) :
    IsTopologicallyFinitePresentation O B := by
  obtain ⟨n, π, hπ, hπker⟩ := hA
  exact ⟨n, f.comp π, hf.comp hπ,
    Ideal.fg_ker_comp π.toRingHom f.toRingHom hπker hker hπ⟩

/-- Being topologically of finite presentation is invariant under isomorphism of `O`-algebras. -/
theorem IsTopologicallyFinitePresentation.of_algEquiv (hA : IsTopologicallyFinitePresentation O A)
    (e : A ≃ₐ[O] B) : IsTopologicallyFinitePresentation O B :=
  hA.of_surjective e e.surjective <| by
    rw [(RingHom.injective_iff_ker_eq_bot (e : A →ₐ[O] B)).mp e.injective]
    exact Submodule.fg_bot

/-- The quotient of an algebra topologically of finite presentation by a finitely generated
ideal is topologically of finite presentation. -/
theorem IsTopologicallyFinitePresentation.quotient (hA : IsTopologicallyFinitePresentation O A)
    {J : Ideal A} (hJ : J.FG) : IsTopologicallyFinitePresentation O (A ⧸ J) :=
  hA.of_surjective (Ideal.Quotient.mkₐ O J) (Ideal.Quotient.mkₐ_surjective O J) <| by
    rwa [← RingHom.ker_coe_toRingHom, Ideal.Quotient.mkₐ_ker]

variable (O) in
/-- The restricted power-series algebra `O⟨ξ₁, …, ξₙ⟩` is topologically of finite presentation,
presented by the identity. Together with
`TauCeti.Huber.IsTopologicallyFinitePresentation.quotient`, every quotient
`O⟨ξ₁, …, ξₙ⟩ ⧸ (f₁, …, fₘ)` is topologically of finite presentation. -/
theorem isTopologicallyFinitePresentation_restrictedMvPowerSeriesCompletion (n : ℕ) :
    IsTopologicallyFinitePresentation O (restrictedMvPowerSeriesCompletion n O) :=
  ⟨n, AlgHom.id O _, Function.surjective_id, by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp Function.injective_id]
    exact Submodule.fg_bot⟩

variable (O) in
/-- A complete adic ring of finite ideal type is topologically of finite presentation over itself,
presented with no variables: `O⟨⟩ ≅ O`. -/
theorem isTopologicallyFinitePresentation_self [IsAdicRing O] :
    IsTopologicallyFinitePresentation O O := by
  let _ : UniformSpace O := IsTopologicalAddGroup.rightUniformSpace O
  have : IsUniformAddGroup O := isUniformAddGroup_of_addCommGroup
  let f := weightedRestrictedSubringFinZeroEquiv (fun _ : Fin 0 ↦ ({1} : Set O))
  let e : restrictedMvPowerSeriesCompletion 0 O ≃ₐ[O] O :=
    (restrictedMvPowerSeriesCompletionAlgEquiv 0 O).trans
      (AlgEquiv.ofRingEquiv (f := f) fun a ↦ by simp [f])
  exact (isTopologicallyFinitePresentation_restrictedMvPowerSeriesCompletion O 0).of_algEquiv e

/-! ### The adic topology of a presentation -/

/-- **Presentations are open quotient maps.** Let `I` be a finitely generated ideal of definition
of `O`. If `A` carries the adic topology of `I·A`, then every surjective `O`-algebra homomorphism
`O⟨ξ₁, …, ξₙ⟩ → A` is an open quotient map. -/
theorem isOpenQuotientMap_of_surjective_restrictedMvPowerSeriesCompletion [TopologicalSpace A]
    {I : Ideal O} (hI : IsAdic I) (hfg : I.FG) (hA : IsAdic (I.map (algebraMap O A))) {n : ℕ}
    {π : restrictedMvPowerSeriesCompletion n O →ₐ[O] A} (hπ : Function.Surjective π) :
    IsOpenQuotientMap π := by
  have hmap : (I.map (algebraMap O (restrictedMvPowerSeriesCompletion n O))).map π.toRingHom =
      I.map (algebraMap O A) := by
    rw [Ideal.map_map]
    exact congrArg (Ideal.map · I) (RingHom.ext π.commutes)
  exact IsAdic.isOpenQuotientMap_of_surjective
    (isAdic_map_algebraMap_restrictedMvPowerSeriesCompletion n hI hfg) (f := π.toRingHom) hπ
    (hmap ▸ hA)

/-- **An algebra topologically of finite presentation is strictly topologically of finite type.**
If `A` is topologically of finite presentation over `O` and carries the adic topology of `I·A`
for a finitely generated ideal of definition `I` of `O`, then any presentation exhibits `A` as an
open quotient of `O⟨ξ₁, …, ξₙ⟩` (Bosch–Lütkebohmert I, §1). -/
theorem IsTopologicallyFinitePresentation.isStrictlyTopologicallyFiniteType [TopologicalSpace A]
    (h : IsTopologicallyFinitePresentation O A) {I : Ideal O} (hI : IsAdic I) (hfg : I.FG)
    (hA : IsAdic (I.map (algebraMap O A))) :
    IsStrictlyTopologicallyFiniteType (algebraMap O A) := by
  obtain ⟨n, π, hπ, -⟩ := h
  exact isStrictlyTopologicallyFiniteType_iff.mpr ⟨n, π.toRingHom,
    isOpenQuotientMap_of_surjective_restrictedMvPowerSeriesCompletion hI hfg hA hπ,
    π.comp_algebraMap⟩

/-! ### Reductions modulo an ideal of definition -/

section Reduction

variable [IsAdicRing O]

/-- **Reductions of algebras topologically of finite presentation are finitely presented.** If
`O` is an adic ring of finite ideal type, `I` is a finitely generated ideal of definition of `O`
and `A` is topologically of finite presentation over `O`, then `A ⧸ I·A` is a finitely presented
`O ⧸ I`-algebra: a presentation `O⟨ξ⟩ ⧸ 𝔞 ≅ A` reduces to an isomorphism of `A ⧸ I·A` with the
quotient of `(O ⧸ I)[ξ]` by the image of `𝔞` (Bosch–Lütkebohmert I, §1). -/
theorem IsTopologicallyFinitePresentation.finitePresentation_quotient
    (h : IsTopologicallyFinitePresentation O A) {I : Ideal O} (hI : IsAdic I) (hfg : I.FG) :
    Algebra.FinitePresentation (O ⧸ I) (A ⧸ I.map (algebraMap O A)) := by
  obtain ⟨n, π, hπ, hπker⟩ := h
  let _ : UniformSpace O := IsTopologicalAddGroup.rightUniformSpace O
  have : IsUniformAddGroup O := isUniformAddGroup_of_addCommGroup
  set P := restrictedMvPowerSeriesCompletion n O
  set IP := I.map (algebraMap O P)
  set IA := I.map (algebraMap O A)
  -- `O⟨ξ⟩ ⧸ I·O⟨ξ⟩` is the polynomial algebra `(O ⧸ I)[ξ]`
  let e := quotientRestrictedCompletionEquivMvPolynomialQuotient (k := n) hI hfg
  -- the reduction `O⟨ξ⟩ → A ⧸ I·A` of the presentation has kernel `I·O⟨ξ⟩ + ker π`
  let π' : P →+* A := π
  let g : P →+* A ⧸ IA := (Ideal.Quotient.mk IA).comp π'
  have hmap : IP.map π' = IA := by
    rw [Ideal.map_map]
    exact congrArg (Ideal.map · I) (RingHom.ext π.commutes)
  have hgker : RingHom.ker g = IP ⊔ RingHom.ker π' := by
    rw [← RingHom.comap_ker, Ideal.mk_ker, ← hmap, Ideal.comap_map_of_surjective' π' hπ]
  have hle : ∀ x ∈ IP, g x = 0 := fun x hx ↦ RingHom.mem_ker.mp (hgker ▸ Ideal.mem_sup_left hx)
  -- it factors through `(O ⧸ I)[ξ]`, surjectively and with finitely generated kernel
  let gbar := Ideal.Quotient.lift IP g hle
  let ψ : MvPolynomial (Fin n) (O ⧸ I) →+* A ⧸ IA :=
    gbar.comp (e.toRingEquiv.symm : MvPolynomial (Fin n) (O ⧸ I) →+* P ⧸ IP)
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp hπ
  have hψ : Function.Surjective ψ :=
    (Ideal.Quotient.lift_surjective_of_surjective IP hle hg).comp e.symm.surjective
  have hψker : (RingHom.ker ψ).FG := by
    have hgbar : RingHom.ker gbar = (RingHom.ker g).map (Ideal.Quotient.mk IP) :=
      Ideal.ker_quotient_lift g hle
    rw [← RingHom.comap_ker, Ideal.comap_coe, Ideal.comap_symm, hgbar, hgker]
    rw [← Ideal.map_coe]
    exact Ideal.FG.map (Ideal.FG.map (Submodule.FG.sup (Ideal.FG.map hfg _) hπker) _) _
  let ψₐ : MvPolynomial (Fin n) (O ⧸ I) →ₐ[O ⧸ I] A ⧸ IA :=
    { ψ with
      commutes' := fun r ↦ by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
        have he : e.symm (algebraMap (O ⧸ I) _ (Ideal.Quotient.mk I a)) =
            Ideal.Quotient.mk IP (algebraMap O P a) := by
          rw [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply, AlgEquiv.commutes,
            Ideal.Quotient.mk_algebraMap]
        simp only [ψ, RingHom.toFun_eq_coe, RingHom.comp_apply, RingEquiv.coe_toRingHom,
          AlgEquiv.toRingEquiv_symm, AlgEquiv.coe_toRingEquiv, he, gbar, Ideal.Quotient.lift_mk]
        simp only [g, π', RingHom.comp_apply, AlgHom.coe_toRingHom, AlgHom.commutes,
          Ideal.Quotient.mk_algebraMap]
        rw [IsScalarTower.algebraMap_apply O (O ⧸ I) (A ⧸ IA), Ideal.Quotient.algebraMap_eq] }
  exact Algebra.FinitePresentation.of_surjective (f := ψₐ) hψ hψker

end Reduction

/-- **Reductions modulo powers of a pseudouniformiser.** If `O` is a complete rank-one valuation
base with pseudouniformiser `ϖ` and `A` is topologically of finite presentation over `O`, then
each `A ⧸ ϖᵐA` is a finitely presented `O ⧸ ϖᵐ`-algebra (Bosch–Lütkebohmert I, §1). -/
theorem IsTopologicallyFinitePresentation.finitePresentation_quotient_pow
    (h : IsTopologicallyFinitePresentation O A) (ϖ : O) [IsCompleteRankOneBase O ϖ] (m : ℕ) :
    Algebra.FinitePresentation (O ⧸ Ideal.span {ϖ ^ m})
      (A ⧸ (Ideal.span {ϖ ^ m}).map (algebraMap O A)) := by
  rcases m.eq_zero_or_pos with rfl | hm
  · -- modulo `ϖ⁰ = 1` both rings are zero
    have : Subsingleton (O ⧸ Ideal.span {ϖ ^ 0}) := Ideal.Quotient.subsingleton_iff.mpr (by simp)
    have : Subsingleton (A ⧸ (Ideal.span {ϖ ^ 0}).map (algebraMap O A)) :=
      Ideal.Quotient.subsingleton_iff.mpr (by simp [Ideal.map_top])
    refine Algebra.FinitePresentation.of_surjective (f := Algebra.ofId _ _)
      (fun _ ↦ ⟨0, Subsingleton.elim _ _⟩) ?_
    rw [Subsingleton.elim (RingHom.ker _) ⊥]
    exact Submodule.fg_bot
  · have := IsCompleteRankOneBase.isAdicRing ϖ
    rw [← Ideal.span_singleton_pow]
    exact h.finitePresentation_quotient (is_ideal_adic_pow IsCompleteRankOneBase.isAdic hm)
      (Submodule.FG.pow ⟨{ϖ}, by simp⟩ m)

/-! ### Admissible algebras -/

/-- **Admissible means topologically of finite presentation and flat.** Over a valuation ring `O`
that is separated for the `ϖ`-adic topology, with `ϖ ≠ 0`, an `O`-algebra is admissible exactly
when it is topologically of finite presentation and flat over `O`: having no `ϖ`-torsion means
having no torsion at all, and torsion-free modules over the Bézout domain `O` are flat
(Bosch–Lütkebohmert I, §1, p. 293). -/
theorem isAdmissibleAlgebra_iff_flat [IsDomain O] [ValuationRing O] {ϖ : O} (hϖ : ϖ ≠ 0)
    [IsHausdorff (Ideal.span {ϖ}) O] :
    IsAdmissibleAlgebra ϖ A ↔ IsTopologicallyFinitePresentation O A ∧ Module.Flat O A := by
  refine ⟨fun h ↦ ⟨h.isTopologicallyFinitePresentation, ?_⟩, fun h ↦ ⟨h.1, ?_⟩⟩
  · have hϖA : IsSMulRegular A ϖ :=
      (isSMulRegular_iff_torsionBy_eq_bot A ϖ).mpr h.torsionBy_eq_bot
    refine Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr (eq_bot_iff.mpr fun x hx ↦ ?_)
    obtain ⟨⟨a, ha⟩, hax⟩ := (Submodule.mem_torsion_iff x).mp hx
    exact hϖA.of_isHausdorff (nonZeroDivisors.ne_zero ha) (by simpa using hax)
  · have := h.2
    exact (isSMulRegular_iff_torsionBy_eq_bot A ϖ).mp
      (Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hϖ))

section Restricted

variable [IsDomain O] [IsAdicRing O]

/-- Over a complete adic domain, multiplication by a nonzero scalar is injective on
`O⟨ξ₁, …, ξₙ⟩`: restricted power series are multiplied by a scalar coefficientwise. -/
theorem isSMulRegular_restrictedMvPowerSeriesCompletion (n : ℕ) {a : O} (ha : a ≠ 0) :
    IsSMulRegular (restrictedMvPowerSeriesCompletion n O) a := by
  let _ : UniformSpace O := IsTopologicalAddGroup.rightUniformSpace O
  have : IsUniformAddGroup O := isUniformAddGroup_of_addCommGroup
  let e := restrictedMvPowerSeriesCompletionAlgEquiv n O
  intro x y hxy
  apply e.injective
  ext ν
  have h' : a • e x = a • e y := by
    rw [← map_smul, ← map_smul]
    exact congrArg e hxy
  have h := congrArg (fun z ↦ MvPowerSeries.coeff ν (Subtype.val z)) h'
  simp only [Algebra.smul_def, algebraMap_weightedRestrictedSubring, Subring.coe_mul,
    coe_weightedC, MvPowerSeries.coeff_C_mul] at h
  exact mul_left_cancel₀ ha h

variable (O) in
/-- Over a complete adic domain, the restricted power-series algebra `O⟨ξ₁, …, ξₙ⟩` is admissible
for every nonzero `ϖ`. -/
theorem isAdmissibleAlgebra_restrictedMvPowerSeriesCompletion {ϖ : O} (hϖ : ϖ ≠ 0) (n : ℕ) :
    IsAdmissibleAlgebra ϖ (restrictedMvPowerSeriesCompletion n O) :=
  ⟨isTopologicallyFinitePresentation_restrictedMvPowerSeriesCompletion O n,
    (isSMulRegular_iff_torsionBy_eq_bot _ ϖ).mp
      (isSMulRegular_restrictedMvPowerSeriesCompletion n hϖ)⟩

end Restricted

end TauCeti.Huber
