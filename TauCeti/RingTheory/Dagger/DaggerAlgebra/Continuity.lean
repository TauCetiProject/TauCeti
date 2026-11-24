/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.DaggerAlgebra.Map
public import TauCeti.RingTheory.Dagger.DaggerAlgebra.ResidueNorm

import TauCeti.RingTheory.Affinoid.Continuity
import TauCeti.RingTheory.Affinoid.PowerBounded
import TauCeti.RingTheory.Dagger.DaggerAlgebra.FaithfullyFlat
import TauCeti.RingTheory.Dagger.QuotientCompletion
import TauCeti.RingTheory.Dagger.TateLift

/-!
# Automatic continuity and the canonical topology of dagger algebras

Let `K` be a complete nontrivially normed ultrametric field and `A` a `K`-dagger algebra. Equipping
`A` with the residue norm `TauCeti.Dagger.residueNormedCommRing` of its chosen minimal presentation
`W_n ↠ A` identifies `A` isometrically with `W_n ⧸ ker (presentation K A)`
(`TauCeti.Dagger.residueContinuousAlgEquiv`) and embeds `A` isometrically as a dense `K`-subalgebra
of its affinoid completion `Â = completion K A` (`TauCeti.Dagger.isometry_toCompletion`,
`TauCeti.Dagger.denseRange_toCompletion`). Combined with the universal extension to Tate quotients
(`TauCeti.Dagger.washnitzerAlgebra.liftToTateQuotient`), this yields the topological theory of
dagger algebras:

* **Automatic continuity** (`AlgHom.continuous_washnitzerAlgebra_quotient`,
  `AlgHom.continuous_of_isDaggerAlgebra`): every `K`-algebra homomorphism between
  Monsky–Washnitzer presentation quotients `W_σ ⧸ I →ₐ[K] W_τ ⧸ J`, and hence (via
  `TauCeti.Dagger.residueContinuousAlgEquiv`) every `K`-algebra homomorphism `φ : A →ₐ[K] B` of
  dagger algebras, is continuous and norm-bounded with no topological hypothesis on `φ`. Indeed any
  map out of `W_σ ⧸ I` into an affinoid target factors through the isometric embedding
  `W_σ ⧸ I → T_σ ⧸ I T_σ` (`Ideal.isometry_quotientMap_toTate`) and automatic continuity on affinoid
  algebras (`TauCeti.IsAffinoidAlgebra.continuous_algHom`).
* **Canonical topology and presentation independence**
  (`AlgHom.washnitzerPresentationContinuousAlgEquiv`,
  `AlgHom.daggerPresentationResidueContinuousAlgEquiv`,
  `AlgEquiv.toContinuousAlgEquivOfIsDaggerAlgebra`): all Monsky–Washnitzer presentations
  `π : W_σ ↠ A` induce Lipschitz-equivalent residue norms and hence the same topology on `A`. Every
  surjective morphism `φ : A →ₐ[K] B` of dagger algebras is an open quotient map
  (`AlgHom.isOpenQuotientMap_of_isDaggerAlgebra`) inducing a topological `K`-algebra
  isomorphism `A ⧸ ker φ ≃A[K] B` (`AlgHom.quotientKerContinuousAlgEquivOfIsDaggerAlgebra`),
  and every ideal of `A` is closed (`Ideal.isClosed_of_isDaggerAlgebra`).
* **Power-bounded and topologically nilpotent elements**
  (`TauCeti.Dagger.IsDaggerAlgebra.isPowerBounded_iff_supSeminorm_le_one`,
  `TauCeti.Dagger.IsDaggerAlgebra.isTopologicallyNilpotent_iff_supSeminorm_lt_one`): in the
  canonical topology on `A`, the power-bounded elements are `{a | |a|sup ≤ 1}` (preserved by
  arbitrary `K`-algebra homomorphisms via `AlgHom.isPowerBounded_map_of_isDaggerAlgebra`) and
  the topologically nilpotent elements are `{a | |a|sup < 1}` (preserved via automatic continuity
  and `IsTopologicallyNilpotent.map`).

## Main definitions

* `AlgHom.washnitzerPresentationContinuousAlgEquiv`: the canonical topological `K`-algebra
  isomorphism `(W_σ ⧸ ker π₁) ≃A[K] (W_τ ⧸ ker π₂)` between any two overconvergent presentations of
  the same `K`-algebra.
* `AlgHom.daggerPresentationResidueContinuousAlgEquiv`: topological `K`-algebra comparison between
  `(A, residueNormedCommRing K A)` and `W_σ ⧸ ker π` for any presentation `π : W_σ ↠ A`.
* `AlgEquiv.toContinuousAlgEquivOfIsDaggerAlgebra`: upgrades an algebraic isomorphism
  `A ≃ₐ[K] B` of dagger algebras to a topological `K`-algebra isomorphism `A ≃A[K] B`.
* `AlgHom.quotientKerContinuousAlgEquivOfIsDaggerAlgebra`: the continuous first isomorphism
  theorem `(A ⧸ ker φ) ≃A[K] B` for a surjective morphism `φ : A →ₐ[K] B` of dagger algebras.

## Main results

* `AlgHom.continuous_washnitzerAlgebra_quotient`, `AlgHom.continuous_of_isDaggerAlgebra`:
  automatic continuity of `K`-algebra homomorphisms between presentation quotients and between
  dagger algebras.
* `AlgHom.exists_pos_forall_norm_washnitzerPresentationContinuousAlgEquiv`: two-sided Lipschitz
  equivalence of residue norms from any two presentations.
* `Ideal.isClosed_of_isDaggerAlgebra`, `AlgHom.isOpenQuotientMap_of_isDaggerAlgebra`: closedness
  of ideals and openness of surjective morphisms of dagger algebras.
* `TauCeti.Dagger.IsDaggerAlgebra.supSeminorm_le_norm`,
  `TauCeti.Dagger.IsDaggerAlgebra.isPowerBounded_iff_supSeminorm_le_one`,
  `TauCeti.Dagger.IsDaggerAlgebra.isTopologicallyNilpotent_iff_supSeminorm_lt_one`: comparison of
  residue norms, `supSeminorm`, power-boundedness, and topological nilpotence.
* `TauCeti.Dagger.washnitzerAlgebra.continuous_algHom_of_finiteDimensional`: automatic continuity
  from the (incomplete) algebra `W_σ` into finite-dimensional topological `K`-algebras.
* `TauCeti.Dagger.completionQuotientEquiv`, `TauCeti.Dagger.isEmbedding_toCompletion_quotient`:
  the completion of `W_σ ⧸ I` is `T_σ ⧸ I T_σ`, and `toCompletion` is a topological embedding for
  the quotient Gauss norm.
* `TauCeti.Dagger.IsDaggerAlgebra.continuous_algHom_of_isInducing`,
  `TauCeti.Dagger.IsDaggerAlgebra.uniformContinuous_algHom_of_isInducing`, and
  `TauCeti.Dagger.IsDaggerAlgebra.isPowerBounded_map`: automatic (uniform) continuity and
  preservation of power-boundedness for any topologies induced from the affinoid completions.
* `TauCeti.Dagger.exists_mul_norm_le_and_norm_le_mul_quotientKerAlgEquivOfSurjective_symm` and
  `TauCeti.Dagger.induced_quotientKerAlgEquivOfSurjective_symm_toUniformSpace`: every presentation
  residue norm is bi-Lipschitz equivalent to `residueNormedCommRing K A` and induces the same
  uniformity.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1, Proposition 1.6 and §1.9.

The presentation-comparison and quotient-topology API parallels
`TauCeti.RingTheory.Affinoid.QuotientNorm`, replacing Banach open mapping on complete affinoid
algebras by factorization through isometric embeddings into affinoid completions.
-/

public section

open Filter Topology

namespace TauCeti.Dagger

open _root_.MvPowerSeries

section PresentationQuotients

namespace washnitzerAlgebra

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {σ : Type*} [Finite σ]

local notation "W " α:max => washnitzerAlgebra α K
local notation "T " α:max => IsRestricted.subring (R := K) (fun _ : α ↦ (1 : ℝ))

/-- Every `K`-algebra homomorphism from a Monsky–Washnitzer presentation quotient `W_σ ⧸ I` into a
completely normed affinoid algebra is continuous for the quotient Gauss norm on `W_σ ⧸ I`. -/
theorem continuous_algHom_quotient_of_isAffinoidAlgebra {S : Type*} [NormedCommRing S]
    [NormedAlgebra K S] [IsUltrametricDist S] [CompleteSpace S] (hS : IsAffinoidAlgebra K S)
    {I : Ideal (W σ)} (φ : (W σ ⧸ I) →ₐ[K] S) : Continuous φ := by
  obtain ⟨Φ, rfl, -⟩ := existsUnique_algHom_tateQuotient hS I φ
  have := ((isAffinoidAlgebra_tate (K := K) (σ := σ)).quotient
    (I.map (toTate σ K))).isNoetherianRing
  rw [AlgHom.coe_comp]
  exact (hS.continuous_algHom (B := T σ ⧸ I.map (toTate σ K)) Φ).comp
    I.isometry_quotientMap_toTate.continuous

/-- On a Monsky–Washnitzer presentation quotient `W_σ ⧸ I`, the supremum seminorm is bounded by the
quotient Gauss norm. -/
theorem supSeminorm_quotient_le_norm {I : Ideal (W σ)} (x : W σ ⧸ I) :
    supSeminorm K x ≤ ‖x‖ := by
  obtain ⟨f, rfl, hf⟩ := I.exists_mk_eq_and_norm_eq_washnitzerAlgebra x
  exact (supSeminorm_map_le_norm (φ := Ideal.Quotient.mkₐ K I)
    Ideal.Quotient.mk_surjective f).trans_eq hf

end washnitzerAlgebra

end PresentationQuotients

end TauCeti.Dagger

namespace AlgHom

open TauCeti TauCeti.Dagger _root_.MvPowerSeries

section WashnitzerQuotients

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {σ τ : Type*} [_root_.Finite σ] [_root_.Finite τ]

local notation "W " α:max => washnitzerAlgebra α K
local notation "T " α:max => IsRestricted.subring (R := K) (fun _ : α ↦ (1 : ℝ))

/-- **Automatic continuity on presentation quotients.** Every `K`-algebra homomorphism between
Monsky–Washnitzer presentation quotients is continuous for their quotient Gauss norms. -/
theorem continuous_washnitzerAlgebra_quotient {I : Ideal (W σ)} {J : Ideal (W τ)}
    (φ : (W σ ⧸ I) →ₐ[K] (W τ ⧸ J)) : Continuous φ := by
  let ιJ : (W τ ⧸ J) →ₐ[K] T τ ⧸ J.map (washnitzerAlgebra.toTate τ K) :=
    Ideal.quotientMapₐ (J.map (washnitzerAlgebra.toTate τ K))
      (washnitzerAlgebra.toTate τ K) Ideal.le_comap_map
  refine J.isometry_quotientMap_toTate.isEmbedding.isInducing.continuous_iff.mpr ?_
  rw [← AlgHom.coe_comp]
  exact washnitzerAlgebra.continuous_algHom_quotient_of_isAffinoidAlgebra (K := K) (σ := σ)
    (S := T τ ⧸ J.map (washnitzerAlgebra.toTate τ K)) (I := I)
    ((isAffinoidAlgebra_tate (K := K) (σ := τ)).quotient (J.map (washnitzerAlgebra.toTate τ K)))
    (ιJ.comp φ)

/-- Every `K`-algebra homomorphism between Monsky–Washnitzer presentation quotients is bounded for
their quotient Gauss norms. -/
theorem exists_pos_forall_norm_map_le_washnitzerAlgebra_quotient {I : Ideal (W σ)}
    {J : Ideal (W τ)} (φ : (W σ ⧸ I) →ₐ[K] (W τ ⧸ J)) :
    ∃ C > 0, ∀ x : W σ ⧸ I, ‖φ x‖ ≤ C * ‖x‖ :=
  (⟨φ.toLinearMap, φ.continuous_washnitzerAlgebra_quotient⟩ : (W σ ⧸ I) →L[K] (W τ ⧸ J)).bound

end WashnitzerQuotients

end AlgHom

namespace AlgEquiv

open TauCeti TauCeti.Dagger

section WashnitzerQuotients

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {σ τ : Type*} [Finite σ] [Finite τ]

local notation "W " α:max => washnitzerAlgebra α K

/-- Every `K`-algebra isomorphism between Monsky–Washnitzer presentation quotients is a topological
`K`-algebra isomorphism for their quotient Gauss norms. -/
noncomputable def washnitzerQuotientContinuousAlgEquiv {I : Ideal (W σ)} {J : Ideal (W τ)}
    (e : (W σ ⧸ I) ≃ₐ[K] (W τ ⧸ J)) : (W σ ⧸ I) ≃A[K] (W τ ⧸ J) :=
  { e with
    continuous_toFun := e.toAlgHom.continuous_washnitzerAlgebra_quotient
    continuous_invFun := e.symm.toAlgHom.continuous_washnitzerAlgebra_quotient }

/-- `e.washnitzerQuotientContinuousAlgEquiv` has the same underlying function as `e`. -/
@[simp]
theorem coe_washnitzerQuotientContinuousAlgEquiv {I : Ideal (W σ)} {J : Ideal (W τ)}
    (e : (W σ ⧸ I) ≃ₐ[K] (W τ ⧸ J)) :
    ⇑e.washnitzerQuotientContinuousAlgEquiv = ⇑e := (rfl)

/-- The underlying `AlgEquiv` of `e.washnitzerQuotientContinuousAlgEquiv` is `e`. -/
@[simp]
theorem toAlgEquiv_washnitzerQuotientContinuousAlgEquiv {I : Ideal (W σ)} {J : Ideal (W τ)}
    (e : (W σ ⧸ I) ≃ₐ[K] (W τ ⧸ J)) :
    e.washnitzerQuotientContinuousAlgEquiv.toAlgEquiv = e := (rfl)

/-- `washnitzerQuotientContinuousAlgEquiv` commutes with `.symm`. -/
@[simp]
theorem washnitzerQuotientContinuousAlgEquiv_symm {I : Ideal (W σ)} {J : Ideal (W τ)}
    (e : (W σ ⧸ I) ≃ₐ[K] (W τ ⧸ J)) :
    e.washnitzerQuotientContinuousAlgEquiv.symm =
      e.symm.washnitzerQuotientContinuousAlgEquiv := by
  ext x
  exact e.washnitzerQuotientContinuousAlgEquiv.symm_apply_eq.mpr (by simp)

end WashnitzerQuotients

end AlgEquiv

namespace AlgHom

open TauCeti TauCeti.Dagger

section WashnitzerPresentations

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {σ τ : Type*} [_root_.Finite σ] [_root_.Finite τ]

local notation "W " α:max => washnitzerAlgebra α K

/-- **Presentation independence of the residue-norm topology.** Two Monsky–Washnitzer presentations
`π₁ : W_σ ↠ C` and `π₂ : W_τ ↠ C` of the same `K`-algebra give residue algebras whose quotient Gauss
norms define the same topology: the canonical `K`-algebra isomorphism compatible with both
presentations is a homeomorphism. -/
noncomputable def washnitzerPresentationContinuousAlgEquiv {C : Type*} [CommRing C] [Algebra K C]
    (π₁ : W σ →ₐ[K] C) (hπ₁ : Function.Surjective π₁)
    (π₂ : W τ →ₐ[K] C) (hπ₂ : Function.Surjective π₂) :
    (W σ ⧸ RingHom.ker π₁) ≃A[K] (W τ ⧸ RingHom.ker π₂) :=
  ((Ideal.quotientKerAlgEquivOfSurjective hπ₁).trans
    (Ideal.quotientKerAlgEquivOfSurjective hπ₂).symm).washnitzerQuotientContinuousAlgEquiv

/-- `π₁.washnitzerPresentationContinuousAlgEquiv hπ₁ π₂ hπ₂` maps the quotient class of `f` to that
of any `g` with `π₂ g = π₁ f`. -/
theorem washnitzerPresentationContinuousAlgEquiv_mk {C : Type*} [CommRing C] [Algebra K C]
    (π₁ : W σ →ₐ[K] C) (hπ₁ : Function.Surjective π₁)
    (π₂ : W τ →ₐ[K] C) (hπ₂ : Function.Surjective π₂)
    {f : W σ} {g : W τ} (h : π₂ g = π₁ f) :
    π₁.washnitzerPresentationContinuousAlgEquiv hπ₁ π₂ hπ₂ (Ideal.Quotient.mk _ f) =
      Ideal.Quotient.mk _ g := by
  simp [washnitzerPresentationContinuousAlgEquiv, ← h]

/-- `washnitzerPresentationContinuousAlgEquiv` is compatible with both presentations via
`Ideal.kerLiftAlg`. -/
@[simp]
theorem kerLiftAlg_washnitzerPresentationContinuousAlgEquiv {C : Type*} [CommRing C] [Algebra K C]
    (π₁ : W σ →ₐ[K] C) (hπ₁ : Function.Surjective π₁)
    (π₂ : W τ →ₐ[K] C) (hπ₂ : Function.Surjective π₂) (x : W σ ⧸ RingHom.ker π₁) :
    Ideal.kerLiftAlg π₂ (π₁.washnitzerPresentationContinuousAlgEquiv hπ₁ π₂ hπ₂ x) =
      Ideal.kerLiftAlg π₁ x := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨g, hg⟩ := hπ₂ (π₁ f)
  rw [π₁.washnitzerPresentationContinuousAlgEquiv_mk hπ₁ π₂ hπ₂ hg]
  simpa using hg

/-- Swapping the two presentations in `washnitzerPresentationContinuousAlgEquiv` yields the inverse
homeomorphism. -/
@[simp]
theorem washnitzerPresentationContinuousAlgEquiv_symm {C : Type*} [CommRing C] [Algebra K C]
    (π₁ : W σ →ₐ[K] C) (hπ₁ : Function.Surjective π₁)
    (π₂ : W τ →ₐ[K] C) (hπ₂ : Function.Surjective π₂) :
    (π₁.washnitzerPresentationContinuousAlgEquiv hπ₁ π₂ hπ₂).symm =
      π₂.washnitzerPresentationContinuousAlgEquiv hπ₂ π₁ hπ₁ := by
  ext x
  simp [washnitzerPresentationContinuousAlgEquiv]

/-- **Equivalence of residue norms across presentations.** For any two Monsky–Washnitzer
presentations of the same `K`-algebra, the induced quotient Gauss norms bound each other up to
positive multiplicative constants. -/
theorem exists_pos_forall_norm_washnitzerPresentationContinuousAlgEquiv {C : Type*} [CommRing C]
    [Algebra K C] (π₁ : W σ →ₐ[K] C) (hπ₁ : Function.Surjective π₁)
    (π₂ : W τ →ₐ[K] C) (hπ₂ : Function.Surjective π₂) :
    ∃ c > 0, ∃ C' > 0, ∀ x : W σ ⧸ RingHom.ker π₁,
      c * ‖x‖ ≤ ‖π₁.washnitzerPresentationContinuousAlgEquiv hπ₁ π₂ hπ₂ x‖ ∧
        ‖π₁.washnitzerPresentationContinuousAlgEquiv hπ₁ π₂ hπ₂ x‖ ≤ C' * ‖x‖ := by
  let e := (Ideal.quotientKerAlgEquivOfSurjective hπ₁).trans
    (Ideal.quotientKerAlgEquivOfSurjective hπ₂).symm
  obtain ⟨C₁, hC₁, hle₁⟩ := e.toAlgHom.exists_pos_forall_norm_map_le_washnitzerAlgebra_quotient
  obtain ⟨C₂, hC₂, hle₂⟩ :=
    e.symm.toAlgHom.exists_pos_forall_norm_map_le_washnitzerAlgebra_quotient
  refine ⟨C₂⁻¹, inv_pos.mpr hC₂, C₁, hC₁, fun x ↦ ⟨?_, hle₁ x⟩⟩
  rw [inv_mul_le_iff₀ hC₂]
  simpa [washnitzerPresentationContinuousAlgEquiv, e] using hle₂ (e x)

end WashnitzerPresentations

end AlgHom

namespace TauCeti.Dagger

section DaggerTopology

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]

namespace IsDaggerAlgebra

/-- Every `K`-algebra homomorphism from a dagger algebra (with its residue norm) into a completely
normed affinoid algebra is continuous. -/
theorem continuous_algHom_of_isAffinoidAlgebra {S : Type*} [NormedCommRing S] [NormedAlgebra K S]
    [IsUltrametricDist S] [CompleteSpace S] (hS : IsAffinoidAlgebra K S) (φ : A →ₐ[K] S) :
    letI := residueNormedCommRing K A
    Continuous φ := by
  let := residueNormedCommRing K A
  let e := residueContinuousAlgEquiv K A
  let ψ := φ.comp e.symm.toAlgEquiv.toAlgHom
  have hcomp : ⇑φ = ⇑ψ ∘ ⇑e :=
    funext fun a ↦ congrArg φ (e.symm_apply_apply a).symm
  rw [hcomp]
  exact (washnitzerAlgebra.continuous_algHom_quotient_of_isAffinoidAlgebra hS ψ).comp e.continuous

end IsDaggerAlgebra

end DaggerTopology

end TauCeti.Dagger

namespace AlgHom

open TauCeti TauCeti.Dagger

section DaggerTopology

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
  [CommRing B] [Algebra K B] [IsDaggerAlgebra K B]

/-- For any surjective presentation `π : W_σ →ₐ[K] A` of a dagger algebra, the first isomorphism
theorem `(W_σ ⧸ ker π) ≃ₐ[K] A` is a topological `K`-algebra isomorphism between the quotient Gauss
norm of `π` and `residueNormedCommRing K A`. -/
noncomputable def daggerPresentationResidueContinuousAlgEquiv {σ : Type*} [_root_.Finite σ]
    (π : washnitzerAlgebra σ K →ₐ[K] A) (hπ : Function.Surjective π) :
    letI := residueNormedCommRing K A
    (washnitzerAlgebra σ K ⧸ RingHom.ker π) ≃A[K] A :=
  letI := residueNormedCommRing K A
  (π.washnitzerPresentationContinuousAlgEquiv hπ
    (presentation K A) (presentation_surjective K A)).trans
    (residueContinuousAlgEquiv K A).symm

/-- `π.daggerPresentationResidueContinuousAlgEquiv hπ` sends the class of `f` to `π f`. -/
@[simp↓]
theorem daggerPresentationResidueContinuousAlgEquiv_mk {σ : Type*} [_root_.Finite σ]
    (π : washnitzerAlgebra σ K →ₐ[K] A) (hπ : Function.Surjective π)
    (f : washnitzerAlgebra σ K) :
    letI := residueNormedCommRing K A
    π.daggerPresentationResidueContinuousAlgEquiv hπ (Ideal.Quotient.mk _ f) = π f := by
  let := residueNormedCommRing K A
  obtain ⟨g, hg⟩ := presentation_surjective K A (π f)
  simp [daggerPresentationResidueContinuousAlgEquiv,
    π.washnitzerPresentationContinuousAlgEquiv_mk hπ
      (presentation K A) (presentation_surjective K A) hg, hg]

/-- The inverse of `π.daggerPresentationResidueContinuousAlgEquiv hπ` sends `π f` to the quotient
class of `f`. -/
@[simp↓]
theorem daggerPresentationResidueContinuousAlgEquiv_symm_apply {σ : Type*} [_root_.Finite σ]
    (π : washnitzerAlgebra σ K →ₐ[K] A) (hπ : Function.Surjective π)
    (f : washnitzerAlgebra σ K) :
    letI := residueNormedCommRing K A
    (π.daggerPresentationResidueContinuousAlgEquiv hπ).symm (π f) = Ideal.Quotient.mk _ f :=
  letI := residueNormedCommRing K A
  (π.daggerPresentationResidueContinuousAlgEquiv hπ).symm_apply_eq.mpr
    (π.daggerPresentationResidueContinuousAlgEquiv_mk hπ f).symm

/-- **Automatic continuity for dagger algebras.** Every `K`-algebra homomorphism `φ : A →ₐ[K] B`
between dagger algebras is continuous for their residue norms, with no continuity hypothesis on `φ`
or on any presentation. -/
theorem continuous_of_isDaggerAlgebra (φ : A →ₐ[K] B) :
    letI := residueNormedCommRing K A
    letI := residueNormedCommRing K B
    Continuous φ := by
  let := residueNormedCommRing K A
  let := residueNormedCommRing K B
  let eA := residueContinuousAlgEquiv K A
  let eB := residueContinuousAlgEquiv K B
  let ψ := eB.toAlgEquiv.toAlgHom.comp (φ.comp eA.symm.toAlgEquiv.toAlgHom)
  have hcomp : ⇑φ = ⇑eB.symm ∘ ⇑ψ ∘ ⇑eA :=
    funext fun a ↦
      ((eB.symm_apply_apply (φ (eA.symm (eA a)))).trans
        (congrArg φ (eA.symm_apply_apply a))).symm
  rw [hcomp]
  exact eB.symm.continuous.comp
    (ψ.continuous_washnitzerAlgebra_quotient.comp eA.continuous)

/-- Every `K`-algebra homomorphism `φ : A →ₐ[K] B` of dagger algebras is norm-bounded for their
residue norms. -/
theorem exists_pos_forall_norm_map_le_of_isDaggerAlgebra (φ : A →ₐ[K] B) :
    letI := residueNormedCommRing K A
    letI := residueNormedCommRing K B
    ∃ C > 0, ∀ a : A, ‖φ a‖ ≤ C * ‖a‖ := by
  let := residueNormedCommRing K A
  let := residueNormedAlgebra K A
  let := residueNormedCommRing K B
  let := residueNormedAlgebra K B
  exact (⟨φ.toLinearMap, φ.continuous_of_isDaggerAlgebra⟩ : A →L[K] B).bound

/-- Every surjective `K`-algebra homomorphism `π : W_σ →ₐ[K] A` from a Monsky–Washnitzer algebra
onto a dagger algebra is an open quotient map for the Gauss norm on `W_σ` and the residue norm on
`A`. -/
theorem isOpenQuotientMap_of_surjective_washnitzerAlgebra {σ : Type*} [_root_.Finite σ]
    (π : washnitzerAlgebra σ K →ₐ[K] A) (hπ : Function.Surjective π) :
    letI := residueNormedCommRing K A
    IsOpenQuotientMap π := by
  let := residueNormedCommRing K A
  let e := π.daggerPresentationResidueContinuousAlgEquiv hπ
  have he : IsOpenQuotientMap e := ⟨e.surjective, e.continuous, e.isOpenMap⟩
  have hcomp : (e : _ → A) ∘ Ideal.Quotient.mk (RingHom.ker π) = π :=
    funext (π.daggerPresentationResidueContinuousAlgEquiv_mk hπ)
  rw [← hcomp]
  exact he.comp (QuotientRing.isOpenQuotientMap_mk (RingHom.ker π))

end DaggerTopology

end AlgHom

namespace AlgEquiv

open TauCeti TauCeti.Dagger

section DaggerTopology

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
  [CommRing B] [Algebra K B] [IsDaggerAlgebra K B]

/-- **Uniqueness of the dagger topology.** Every `K`-algebra isomorphism `e : A ≃ₐ[K] B` between
dagger algebras is a homeomorphism for their residue norms. -/
noncomputable def toContinuousAlgEquivOfIsDaggerAlgebra (e : A ≃ₐ[K] B) :
    letI := residueNormedCommRing K A
    letI := residueNormedCommRing K B
    A ≃A[K] B :=
  letI := residueNormedCommRing K A
  letI := residueNormedCommRing K B
  { e with
    continuous_toFun := e.toAlgHom.continuous_of_isDaggerAlgebra
    continuous_invFun := e.symm.toAlgHom.continuous_of_isDaggerAlgebra }

/-- `e.toContinuousAlgEquivOfIsDaggerAlgebra` has the same underlying function as `e`. -/
@[simp↓]
theorem coe_toContinuousAlgEquivOfIsDaggerAlgebra (e : A ≃ₐ[K] B) :
    letI := residueNormedCommRing K A
    letI := residueNormedCommRing K B
    ⇑e.toContinuousAlgEquivOfIsDaggerAlgebra = ⇑e :=
  letI := residueNormedCommRing K A
  letI := residueNormedCommRing K B
  (rfl)

/-- The underlying `AlgEquiv` of `e.toContinuousAlgEquivOfIsDaggerAlgebra` is `e`. -/
@[simp↓]
theorem toAlgEquiv_toContinuousAlgEquivOfIsDaggerAlgebra (e : A ≃ₐ[K] B) :
    letI := residueNormedCommRing K A
    letI := residueNormedCommRing K B
    e.toContinuousAlgEquivOfIsDaggerAlgebra.toAlgEquiv = e :=
  letI := residueNormedCommRing K A
  letI := residueNormedCommRing K B
  (rfl)

/-- `toContinuousAlgEquivOfIsDaggerAlgebra` commutes with `.symm`. -/
@[simp↓]
theorem toContinuousAlgEquivOfIsDaggerAlgebra_symm (e : A ≃ₐ[K] B) :
    letI := residueNormedCommRing K A
    letI := residueNormedCommRing K B
    e.toContinuousAlgEquivOfIsDaggerAlgebra.symm =
      e.symm.toContinuousAlgEquivOfIsDaggerAlgebra := by
  let := residueNormedCommRing K A
  let := residueNormedCommRing K B
  ext b
  exact e.toContinuousAlgEquivOfIsDaggerAlgebra.symm_apply_eq.mpr (by simp)

end DaggerTopology

end AlgEquiv

namespace TauCeti.Dagger

/-- The chosen minimal presentation `presentation K A : W_n →ₐ[K] A` is an open quotient map onto
`(A, residueNormedCommRing K A)`. -/
theorem isOpenQuotientMap_presentation (K A : Type*) [NontriviallyNormedField K]
    [IsUltrametricDist K] [CompleteSpace K] [CommRing A] [Algebra K A] [IsDaggerAlgebra K A] :
    letI := residueNormedCommRing K A
    IsOpenQuotientMap (presentation K A) :=
  (presentation K A).isOpenQuotientMap_of_surjective_washnitzerAlgebra
    (presentation_surjective K A)

end TauCeti.Dagger

namespace Ideal

open TauCeti TauCeti.Dagger

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]

/-- **Every ideal of a dagger algebra is closed** in its canonical residue-norm topology. -/
theorem isClosed_of_isDaggerAlgebra (J : Ideal A) :
    letI := residueNormedCommRing K A
    IsClosed (J : Set A) := by
  let := residueNormedCommRing K A
  have hc : IsClosed (J.map (toCompletion K A) : Set (completion K A)) :=
    IsAffinoidAlgebra.isClosed_ideal (K := K) (A := completion K A) isAffinoidAlgebra_completion _
  have hpre : (toCompletion K A) ⁻¹' (J.map (toCompletion K A) : Set (completion K A)) = J := by
    rw [← Ideal.coe_comap, comap_map_toCompletion K J]
  exact hpre ▸ hc.preimage (isometry_toCompletion K A).continuous

end Ideal

namespace AlgHom

open TauCeti TauCeti.Dagger

section OpenQuotient

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
  [CommRing B] [Algebra K B] [IsDaggerAlgebra K B]

/-- **Surjective morphisms of dagger algebras are open quotient maps.** Every surjective `K`-algebra
homomorphism `φ : A →ₐ[K] B` between dagger algebras is an open quotient map for their residue
norms, so `B` carries the quotient topology induced by `φ`. -/
theorem isOpenQuotientMap_of_isDaggerAlgebra (φ : A →ₐ[K] B) (hφ : Function.Surjective φ) :
    letI := residueNormedCommRing K A
    letI := residueNormedCommRing K B
    IsOpenQuotientMap φ := by
  let := residueNormedCommRing K A
  let := residueNormedCommRing K B
  rw [← (isOpenQuotientMap_presentation K A).of_comp_iff]
  exact (φ.comp (presentation K A)).isOpenQuotientMap_of_surjective_washnitzerAlgebra
    (hφ.comp (presentation_surjective K A))

/-- **The continuous first isomorphism theorem for dagger algebras.** For a surjective `K`-algebra
homomorphism `φ : A →ₐ[K] B` of dagger algebras, the algebraic isomorphism `A ⧸ ker φ ≃ₐ[K] B` is a
homeomorphism for the quotient topology of `residueNormedCommRing K A` and
`residueNormedCommRing K B`. -/
noncomputable def quotientKerContinuousAlgEquivOfIsDaggerAlgebra
    (φ : A →ₐ[K] B) (hφ : Function.Surjective φ) :
    letI := residueNormedCommRing K A
    letI := residueNormedCommRing K B
    (A ⧸ RingHom.ker φ) ≃A[K] B :=
  letI := residueNormedCommRing K A
  letI := residueNormedCommRing K B
  let e := Ideal.quotientKerAlgEquivOfSurjective hφ
  have hmk : IsOpenQuotientMap (Ideal.Quotient.mk (RingHom.ker φ)) :=
    QuotientRing.isOpenQuotientMap_mk (RingHom.ker φ)
  have hφo : IsOpenQuotientMap φ := φ.isOpenQuotientMap_of_isDaggerAlgebra hφ
  { e with
    continuous_toFun := hmk.continuous_comp_iff.mp <| by
      have hcomp : e.toFun ∘ Ideal.Quotient.mk (RingHom.ker φ) = φ :=
        funext (Ideal.quotientKerAlgEquivOfSurjective_mk hφ)
      rw [hcomp]
      exact hφo.continuous
    continuous_invFun := hφo.continuous_comp_iff.mp <| by
      have hcomp : e.invFun ∘ φ = Ideal.Quotient.mk (RingHom.ker φ) :=
        funext (Ideal.quotientKerAlgEquivOfSurjective_symm_apply hφ)
      rw [hcomp]
      exact continuous_quot_mk }

/-- `φ.quotientKerContinuousAlgEquivOfIsDaggerAlgebra hφ` sends the class of `a` to `φ a`. -/
@[simp↓]
theorem quotientKerContinuousAlgEquivOfIsDaggerAlgebra_mk
    (φ : A →ₐ[K] B) (hφ : Function.Surjective φ) (a : A) :
    letI := residueNormedCommRing K A
    letI := residueNormedCommRing K B
    φ.quotientKerContinuousAlgEquivOfIsDaggerAlgebra hφ (Ideal.Quotient.mk _ a) = φ a :=
  letI := residueNormedCommRing K A
  letI := residueNormedCommRing K B
  Ideal.quotientKerAlgEquivOfSurjective_mk hφ a

/-- The underlying `AlgEquiv` of `φ.quotientKerContinuousAlgEquivOfIsDaggerAlgebra hφ` is
`Ideal.quotientKerAlgEquivOfSurjective hφ`. -/
@[simp↓]
theorem toAlgEquiv_quotientKerContinuousAlgEquivOfIsDaggerAlgebra
    (φ : A →ₐ[K] B) (hφ : Function.Surjective φ) :
    letI := residueNormedCommRing K A
    letI := residueNormedCommRing K B
    (φ.quotientKerContinuousAlgEquivOfIsDaggerAlgebra hφ).toAlgEquiv =
      Ideal.quotientKerAlgEquivOfSurjective hφ :=
  letI := residueNormedCommRing K A
  letI := residueNormedCommRing K B
  (rfl)

end OpenQuotient

end AlgHom

namespace TauCeti.Dagger

section PowerBounded

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]

/-- An element of a dagger algebra is power-bounded in the residue-norm topology iff its image in
`completion K A` is power-bounded. -/
theorem isPowerBounded_toCompletion_iff (a : A) :
    letI := residueNormedCommRing K A
    Huber.IsPowerBounded (toCompletion K A a) ↔ Huber.IsPowerBounded a := by
  let := residueNormedCommRing K A
  let := residueNormedAlgebra K A
  have := isUltrametricDist_residueNormedCommRing K A
  obtain ⟨ϖ, hϖ⟩ := (Huber.IsTateRing.of_normedAlgebra K A).exists_isPseudoUniformizer
  obtain ⟨ϖ', hϖ'⟩ :=
    (Huber.IsTateRing.of_normedAlgebra K (completion K A)).exists_isPseudoUniformizer
  rw [Huber.isPowerBounded_iff, Huber.isPowerBounded_iff,
    hϖ'.isBounded_iff_forall_norm_le, hϖ.isBounded_iff_forall_norm_le]
  simp only [Set.forall_mem_range, ← map_pow, norm_toCompletion]

/-- An element of a dagger algebra is topologically nilpotent in the residue-norm topology iff its
image in `completion K A` is topologically nilpotent. -/
theorem isTopologicallyNilpotent_toCompletion_iff (a : A) :
    letI := residueNormedCommRing K A
    IsTopologicallyNilpotent (toCompletion K A a) ↔ IsTopologicallyNilpotent a := by
  let := residueNormedCommRing K A
  have hfun : (fun n : ℕ ↦ (toCompletion K A a) ^ n) =
      (toCompletion K A) ∘ (fun n : ℕ ↦ a ^ n) :=
    funext fun n ↦ (map_pow (toCompletion K A) a n).symm
  unfold IsTopologicallyNilpotent
  rw [hfun, ← map_zero (toCompletion K A),
    (isometry_toCompletion K A).isEmbedding.isInducing.tendsto_nhds_iff]

namespace IsDaggerAlgebra

/-- **The supremum seminorm is bounded by the residue norm** on a dagger algebra:
`|a|sup ≤ ‖a‖`. -/
theorem supSeminorm_le_norm (a : A) :
    letI := residueNormedCommRing K A
    supSeminorm K a ≤ ‖a‖ := by
  let := residueNormedCommRing K A
  simpa only [AlgEquiv.supSeminorm_eq, norm_residueAlgEquiv] using
    washnitzerAlgebra.supSeminorm_quotient_le_norm (residueAlgEquiv K A a)

/-- **Power-bounded elements of a dagger algebra.** In the canonical residue-norm topology on `A`,
an element is power-bounded if and only if its supremum seminorm is at most one. -/
theorem isPowerBounded_iff_supSeminorm_le_one {a : A} :
    letI := residueNormedCommRing K A
    Huber.IsPowerBounded a ↔ supSeminorm K a ≤ 1 := by
  let := residueNormedCommRing K A
  exact (isPowerBounded_toCompletion_iff (K := K) a).symm.trans <|
    (IsAffinoidAlgebra.isPowerBounded_iff_supSeminorm_le_one (K := K) (A := completion K A)
      isAffinoidAlgebra_completion (f := toCompletion K A a)).trans
      (by rw [supSeminorm_toCompletion])

/-- **Topologically nilpotent elements of a dagger algebra.** In the canonical residue-norm topology
on `A`, an element is topologically nilpotent if and only if its supremum seminorm is strictly less
than one. -/
theorem isTopologicallyNilpotent_iff_supSeminorm_lt_one {a : A} :
    letI := residueNormedCommRing K A
    IsTopologicallyNilpotent a ↔ supSeminorm K a < 1 := by
  let := residueNormedCommRing K A
  exact (isTopologicallyNilpotent_toCompletion_iff (K := K) a).symm.trans <|
    (IsAffinoidAlgebra.isTopologicallyNilpotent_iff_supSeminorm_lt_one (K := K)
      (A := completion K A) isAffinoidAlgebra_completion (f := toCompletion K A a)).trans
      (by rw [supSeminorm_toCompletion])

end IsDaggerAlgebra

end PowerBounded

end TauCeti.Dagger

namespace AlgHom

open TauCeti TauCeti.Dagger

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
  [CommRing B] [Algebra K B] [IsDaggerAlgebra K B]

/-- Every `K`-algebra homomorphism `φ : A →ₐ[K] B` of dagger algebras maps power-bounded elements to
power-bounded elements. -/
theorem isPowerBounded_map_of_isDaggerAlgebra (φ : A →ₐ[K] B) {a : A} :
    letI := residueNormedCommRing K A
    letI := residueNormedCommRing K B
    Huber.IsPowerBounded a → Huber.IsPowerBounded (φ a) :=
  letI := residueNormedCommRing K A
  letI := residueNormedCommRing K B
  fun ha ↦ (IsDaggerAlgebra.isPowerBounded_iff_supSeminorm_le_one (K := K) (a := φ a)).mpr <|
    (φ.supSeminorm_map_le_of_isDaggerAlgebra a).trans
      ((IsDaggerAlgebra.isPowerBounded_iff_supSeminorm_le_one (K := K) (a := a)).mp ha)

end AlgHom

/-! ### Automatic continuity from `W_σ` into finite-dimensional algebras -/

namespace TauCeti.Dagger

open _root_.MvPowerSeries

namespace washnitzerAlgebra

variable {K σ : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Finite σ]

local notation "W " α:max => washnitzerAlgebra α K

/-- **Automatic continuity from `W_σ` into finite-dimensional algebras.** Every `K`-algebra
homomorphism from a Monsky–Washnitzer algebra into a finite-dimensional topological `K`-algebra is
continuous. The target need not be commutative, Hausdorff, or complete. -/
theorem continuous_algHom_of_finiteDimensional {E : Type*} [Ring E] [Algebra K E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul K E] [Module.Finite K E]
    (f : W σ →ₐ[K] E) : Continuous f := by
  let I := RingHom.ker f
  have : Module.Finite K (W σ ⧸ I) :=
    Module.Finite.equiv (Ideal.quotientKerEquivRange f).symm.toLinearEquiv
  let g : W σ ⧸ I →ₐ[K] E := Ideal.kerLiftAlg f
  have hg : Continuous g := g.toLinearMap.continuous_of_finiteDimensional
  exact (hg.comp continuous_quot_mk).congr fun x ↦ Ideal.kerLiftAlg_mk f x

end washnitzerAlgebra

/-! ### Continuity of the completion lift and completions of presentation quotients -/

section CompletionLift

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A C : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
  [NormedCommRing C] [NormedAlgebra K C] [IsUltrametricDist C] [CompleteSpace C]

/-- `completionLift hC χ` into a completely normed affinoid algebra is continuous. -/
theorem continuous_completionLift (hC : IsAffinoidAlgebra K C) (χ : A →ₐ[K] C) :
    Continuous (completionLift hC χ) :=
  have := (isAffinoidAlgebra_completion (K := K) (A := A)).isNoetherianRing
  IsAffinoidAlgebra.continuous_algHom (K := K) (A := C) (B := completion K A) hC
    (completionLift hC χ)

end CompletionLift

section PresentationCompletion

variable {K σ : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Finite σ]

local notation "W " α:max => washnitzerAlgebra α K
local notation "T " α:max => IsRestricted.subring (R := K) (fun _ : α ↦ (1 : ℝ))

/-- **The affinoid completion of a presentation quotient `W_σ ⧸ I` is `T_σ ⧸ I T_σ`**, compatibly
with `toCompletion` and `toTate`. -/
noncomputable def completionQuotientEquiv (I : Ideal (W σ)) :
    completion K (W σ ⧸ I) ≃A[K] (T σ ⧸ I.map (washnitzerAlgebra.toTate σ K)) :=
  ((Ideal.Quotient.mkₐ K I).daggerPresentationCompletionContinuousAlgEquiv
    (Ideal.Quotient.mkₐ_surjective K I)).trans <|
    IsAffinoidAlgebra.toContinuousAlgEquiv (K := K)
      (A := T σ ⧸ (RingHom.ker (Ideal.Quotient.mkₐ K I)).map (washnitzerAlgebra.toTate σ K))
      (B := T σ ⧸ I.map (washnitzerAlgebra.toTate σ K))
      ((isAffinoidAlgebra_tate (K := K) (σ := σ)).quotient _)
      (Ideal.quotientEquivAlgOfEq K
        (congrArg (Ideal.map (washnitzerAlgebra.toTate σ K)) (Ideal.Quotient.mkₐ_ker K I)))

/-- `completionQuotientEquiv I` sends `toCompletion` of the class of `f` to the class of
`toTate σ K f`. -/
@[simp]
theorem completionQuotientEquiv_toCompletion_mk (I : Ideal (W σ)) (f : W σ) :
    completionQuotientEquiv I (toCompletion K (W σ ⧸ I) (Ideal.Quotient.mk I f)) =
      Ideal.Quotient.mk (I.map (washnitzerAlgebra.toTate σ K))
        (washnitzerAlgebra.toTate σ K f) := by
  have h := (Ideal.Quotient.mkₐ K I).daggerPresentationCompletionContinuousAlgEquiv_toCompletion
    (Ideal.Quotient.mkₐ_surjective K I) f
  rw [Ideal.Quotient.mkₐ_eq_mk] at h
  rw [completionQuotientEquiv, ContinuousAlgEquiv.trans_apply, h,
    IsAffinoidAlgebra.coe_toContinuousAlgEquiv, Ideal.quotientEquivAlgOfEq_mk]

/-- The inverse of `completionQuotientEquiv I` sends the class of `toTate σ K f` to
`toCompletion K (W_σ ⧸ I) (Ideal.Quotient.mk I f)`. -/
@[simp]
theorem completionQuotientEquiv_symm_mk_toTate (I : Ideal (W σ)) (f : W σ) :
    (completionQuotientEquiv I).symm
        (Ideal.Quotient.mk (I.map (washnitzerAlgebra.toTate σ K))
          (washnitzerAlgebra.toTate σ K f)) =
      toCompletion K (W σ ⧸ I) (Ideal.Quotient.mk I f) :=
  (completionQuotientEquiv I).symm_apply_eq.mpr
    (completionQuotientEquiv_toCompletion_mk I f).symm

/-- On `W_σ` with its Gauss norm, `toCompletion` is a topological embedding. -/
theorem isEmbedding_toCompletion_washnitzerAlgebra :
    Topology.IsEmbedding (toCompletion K (W σ)) := by
  have h : ⇑(washnitzerAlgebra.completionContinuousAlgEquiv σ K) ∘ ⇑(toCompletion K (W σ)) =
      ⇑(washnitzerAlgebra.toTate σ K) :=
    funext washnitzerAlgebra.completionContinuousAlgEquiv_toCompletion
  exact (washnitzerAlgebra.completionContinuousAlgEquiv σ K).toHomeomorph.isEmbedding.of_comp_iff.mp
    (h ▸ washnitzerAlgebra.isometry_toTate.isEmbedding)

/-- On a presentation quotient `W_σ ⧸ I` with its quotient Gauss norm, `toCompletion` is a
topological embedding. -/
theorem isEmbedding_toCompletion_quotient (I : Ideal (W σ)) :
    Topology.IsEmbedding (toCompletion K (W σ ⧸ I)) := by
  let ιI : W σ ⧸ I →ₐ[K] _ :=
    Ideal.quotientMapₐ (I.map (washnitzerAlgebra.toTate σ K)) (washnitzerAlgebra.toTate σ K)
      Ideal.le_comap_map
  have hι : Isometry ιI := I.isometry_quotientMap_toTate
  have h : ⇑(completionQuotientEquiv I) ∘ ⇑(toCompletion K (W σ ⧸ I)) = ⇑ιI := by
    funext x
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact completionQuotientEquiv_toCompletion_mk I f
  exact (completionQuotientEquiv I).toHomeomorph.isEmbedding.of_comp_iff.mp (h ▸ hι.isEmbedding)

end PresentationCompletion

end TauCeti.Dagger

namespace AlgHom

open TauCeti TauCeti.Dagger

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {σ τ : Type*} [_root_.Finite σ] [_root_.Finite τ]

local notation "W " α:max => washnitzerAlgebra α K

/-- `washnitzerPresentationContinuousAlgEquiv` sends the residue class of `d` in the first
presentation to its residue class in the second presentation. -/
@[simp]
theorem washnitzerPresentationContinuousAlgEquiv_quotientKerAlgEquivOfSurjective_symm
    {D : Type*} [CommRing D] [Algebra K D]
    (π₁ : W σ →ₐ[K] D) (hπ₁ : Function.Surjective π₁)
    (π₂ : W τ →ₐ[K] D) (hπ₂ : Function.Surjective π₂) (d : D) :
    π₁.washnitzerPresentationContinuousAlgEquiv hπ₁ π₂ hπ₂
        ((Ideal.quotientKerAlgEquivOfSurjective hπ₁).symm d) =
      (Ideal.quotientKerAlgEquivOfSurjective hπ₂).symm d := by
  simp [washnitzerPresentationContinuousAlgEquiv]

end AlgHom

/-! ### Automatic continuity for arbitrary inducing topologies and equivalence of residue norms -/

namespace TauCeti.Dagger

section DaggerContinuity

variable {K σ : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Finite σ]

local notation "W " α:max => washnitzerAlgebra α K

namespace IsDaggerAlgebra

variable {A B : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
  [CommRing B] [Algebra K B] [IsDaggerAlgebra K B]

/-- **Automatic continuity of homomorphisms of dagger algebras** (general topology form). If
`toCompletion K A` is continuous and `B` carries the topology induced from `toCompletion K B` — for
instance `W_σ`, `W_σ ⧸ I`, or `residueNormedCommRing` — then every `K`-algebra homomorphism
`φ : A →ₐ[K] B` is continuous. -/
theorem continuous_algHom_of_isInducing [TopologicalSpace A] [TopologicalSpace B]
    (hA : Continuous (toCompletion K A)) (hB : Topology.IsInducing (toCompletion K B))
    (φ : A →ₐ[K] B) : Continuous φ :=
  hB.continuous_iff.mpr <| by
    rw [← AlgHom.coe_comp,
      ← completionLift_comp_toCompletion isAffinoidAlgebra_completion ((toCompletion K B).comp φ)]
    exact (continuous_completionLift (C := completion K B)
      (isAffinoidAlgebra_completion (K := K) (A := B)) ((toCompletion K B).comp φ)).comp hA

/-- **Automatic uniform continuity of homomorphisms of dagger algebras** (general uniformity form).
If `A` and `B` carry uniform additive group structures such that `toCompletion K A` is continuous
and the topology of `B` is induced from `toCompletion K B`, then every `K`-algebra homomorphism
`φ : A →ₐ[K] B` is uniformly continuous. -/
theorem uniformContinuous_algHom_of_isInducing [UniformSpace A] [IsUniformAddGroup A]
    [UniformSpace B] [IsUniformAddGroup B]
    (hA : Continuous (toCompletion K A)) (hB : Topology.IsInducing (toCompletion K B))
    (φ : A →ₐ[K] B) : UniformContinuous φ :=
  uniformContinuous_addMonoidHom_of_continuous (continuous_algHom_of_isInducing hA hB φ)

/-- Every `K`-algebra homomorphism `φ : A →ₐ[K] B` is uniformly continuous for the residue norms. -/
theorem uniformContinuous_algHom (φ : A →ₐ[K] B) :
    letI := residueNormedCommRing K A
    letI := residueNormedCommRing K B
    UniformContinuous φ :=
  letI := residueNormedCommRing K A
  letI := residueNormedCommRing K B
  uniformContinuous_algHom_of_isInducing
    (isometry_toCompletion K A).continuous
    (isometry_toCompletion K B).isEmbedding.isInducing φ

/-- An element of a dagger algebra carrying the topology induced from its affinoid completion is
power-bounded if and only if its image in `completion K A` is power-bounded. -/
theorem isPowerBounded_toCompletion_iff_of_isInducing [TopologicalSpace A]
    (hA : Topology.IsInducing (toCompletion K A)) {a : A} :
    Huber.IsPowerBounded (toCompletion K A a) ↔ Huber.IsPowerBounded a := by
  have hτA : ‹TopologicalSpace A› =
      (residueNormedCommRing K A).toUniformSpace.toTopologicalSpace :=
    hA.eq_induced.trans (residueNormedCommRing_toTopologicalSpace_eq_induced K A).symm
  subst hτA
  exact isPowerBounded_toCompletion_iff a

/-- Every `K`-algebra homomorphism from a dagger algebra (carrying the topology induced from
`toCompletion K A`) into a completely normed `K`-affinoid algebra maps power-bounded elements to
power-bounded elements. -/
theorem isPowerBounded_map_of_isAffinoidAlgebra [TopologicalSpace A]
    (hA : Topology.IsInducing (toCompletion K A))
    {C : Type*} [NormedCommRing C] [NormedAlgebra K C] [IsUltrametricDist C] [CompleteSpace C]
    (hC : IsAffinoidAlgebra K C) (χ : A →ₐ[K] C) {a : A} (ha : Huber.IsPowerBounded a) :
    Huber.IsPowerBounded (χ a) := by
  have := (isAffinoidAlgebra_completion (K := K) (A := A)).isNoetherianRing
  rw [← completionLift_toCompletion hC χ a]
  exact IsAffinoidAlgebra.isPowerBounded_map (K := K) (A := C) (B := completion K A)
    hC (completionLift hC χ) ((isPowerBounded_toCompletion_iff_of_isInducing hA).mpr ha)

/-- Every `K`-algebra homomorphism of dagger algebras maps power-bounded elements to power-bounded
elements (for the canonical topologies induced from `toCompletion`). -/
theorem isPowerBounded_map [TopologicalSpace A] [TopologicalSpace B]
    (hA : Topology.IsInducing (toCompletion K A)) (hB : Topology.IsInducing (toCompletion K B))
    (φ : A →ₐ[K] B) {a : A} (ha : Huber.IsPowerBounded a) :
    Huber.IsPowerBounded (φ a) :=
  (isPowerBounded_toCompletion_iff_of_isInducing hB).mp <|
    isPowerBounded_map_of_isAffinoidAlgebra (C := completion K B) hA
      (isAffinoidAlgebra_completion (K := K) (A := B)) ((toCompletion K B).comp φ) ha

end IsDaggerAlgebra


section NormEquivalence

variable {A : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]

/-- **Bi-Lipschitz equivalence of presentation residue norms** (Grosse-Klönne, Proposition
1.6 (2)). For any surjective presentation `π : W_σ →ₐ[K] A`, the quotient Gauss norm on
`W_σ ⧸ ker π` is bi-Lipschitz equivalent to `residueNormedCommRing K A`. -/
theorem exists_mul_norm_le_and_norm_le_mul_quotientKerAlgEquivOfSurjective_symm
    (π : W σ →ₐ[K] A) (hπ : Function.Surjective π) :
    letI := residueNormedCommRing K A
    ∃ c₁ > 0, ∃ c₂ > 0, ∀ a : A,
      c₁ * ‖a‖ ≤ ‖(Ideal.quotientKerAlgEquivOfSurjective hπ).symm a‖ ∧
        ‖(Ideal.quotientKerAlgEquivOfSurjective hπ).symm a‖ ≤ c₂ * ‖a‖ :=
  letI := residueNormedCommRing K A
  by
    let e := (presentation K A).washnitzerPresentationContinuousAlgEquiv
      (presentation_surjective K A) π hπ
    obtain ⟨c₂, hc₂, hub⟩ := e.toAlgHom.exists_pos_forall_norm_map_le_washnitzerAlgebra_quotient
    obtain ⟨d, hd, hlb⟩ := e.symm.toAlgHom.exists_pos_forall_norm_map_le_washnitzerAlgebra_quotient
    refine ⟨d⁻¹, inv_pos.mpr hd, c₂, hc₂, fun a ↦ ?_⟩
    have he : e (residueAlgEquiv K A a) = (Ideal.quotientKerAlgEquivOfSurjective hπ).symm a := by
      rw [residueAlgEquiv_def]
      exact AlgHom.washnitzerPresentationContinuousAlgEquiv_quotientKerAlgEquivOfSurjective_symm _
        (presentation_surjective K A) π hπ a
    refine ⟨?_, by rw [← he, ← norm_residueAlgEquiv]; exact hub (residueAlgEquiv K A a)⟩
    rw [inv_mul_le_iff₀ hd, ← norm_residueAlgEquiv]
    have hsymm : e.symm.toAlgHom ((Ideal.quotientKerAlgEquivOfSurjective hπ).symm a) =
        residueAlgEquiv K A a := by
      rw [← he, AlgEquiv.toAlgHom_apply, ContinuousAlgEquiv.coe_toAlgEquiv,
        ContinuousAlgEquiv.symm_apply_apply]
    exact hsymm ▸ hlb ((Ideal.quotientKerAlgEquivOfSurjective hπ).symm a)

/-- **Presentation-independence of the induced uniformity.** Every surjective presentation
`π : W_σ →ₐ[K] A` induces the same `UniformSpace A` as `residueNormedCommRing K A`, and hence the
same topology on `A`. -/
theorem induced_quotientKerAlgEquivOfSurjective_symm_toUniformSpace
    (π : W σ →ₐ[K] A) (hπ : Function.Surjective π) :
    (NormedCommRing.induced A (W σ ⧸ RingHom.ker π)
        (Ideal.quotientKerAlgEquivOfSurjective hπ).symm
        (Ideal.quotientKerAlgEquivOfSurjective hπ).symm.injective).toUniformSpace =
      (residueNormedCommRing K A).toUniformSpace := by
  let e₁ := (Ideal.quotientKerAlgEquivOfSurjective hπ).symm
  let e₂ := residueAlgEquiv K A
  let φ := π.washnitzerPresentationContinuousAlgEquiv hπ (presentation K A)
    (presentation_surjective K A)
  have hφ : ⇑φ ∘ ⇑e₁ = ⇑e₂ := funext fun a ↦
    (AlgHom.washnitzerPresentationContinuousAlgEquiv_quotientKerAlgEquivOfSurjective_symm π hπ _
      (presentation_surjective K A) a).trans (by simp only [e₂, residueAlgEquiv_def])
  have h1 : (NormedCommRing.induced A (W σ ⧸ RingHom.ker π) e₁ e₁.injective).toUniformSpace =
      UniformSpace.comap e₁ inferInstance :=
    letI := NormedCommRing.induced A (W σ ⧸ RingHom.ker π) e₁ e₁.injective
    (AddMonoidHomClass.isometry_of_norm e₁ fun _ ↦ rfl).isUniformInducing.comap_uniformSpace.symm
  have h2 : (residueNormedCommRing K A).toUniformSpace =
      UniformSpace.comap e₂ inferInstance :=
    letI := residueNormedCommRing K A
    (AddMonoidHomClass.isometry_of_norm e₂
      (norm_residueAlgEquiv K A)).isUniformInducing.comap_uniformSpace.symm
  rw [h1, h2, ← hφ, UniformSpace.comap_comap,
    φ.isUniformEmbedding.isUniformInducing.comap_uniformSpace]

/-- On `W_σ`, the uniformity of `residueNormedCommRing K (W_σ)` agrees with the Gauss norm
uniformity. -/
theorem residueNormedCommRing_toUniformSpace_washnitzerAlgebra :
    (residueNormedCommRing K (W σ)).toUniformSpace = (inferInstance : UniformSpace (W σ)) :=
  residueNormedCommRing_toUniformSpace_eq isEmbedding_toCompletion_washnitzerAlgebra.isInducing

/-- On a presentation quotient `W_σ ⧸ I`, the uniformity of `residueNormedCommRing K (W_σ ⧸ I)`
agrees with the quotient Gauss norm uniformity. -/
theorem residueNormedCommRing_toUniformSpace_quotient (I : Ideal (W σ)) :
    (residueNormedCommRing K (W σ ⧸ I)).toUniformSpace =
      (inferInstance : UniformSpace (W σ ⧸ I)) :=
  residueNormedCommRing_toUniformSpace_eq (isEmbedding_toCompletion_quotient I).isInducing

end NormEquivalence

/-! ### Edge-case checks -/

section Examples

-- Automatic continuity holds on the zero dagger algebra `W_0 ⧸ ⊤`.
example : Continuous (AlgHom.id K (W (Fin 0) ⧸ (⊤ : Ideal (W (Fin 0))))) :=
  AlgHom.continuous_washnitzerAlgebra_quotient _

-- Automatic continuity holds on nonreduced dagger algebras such as `W_1 ⧸ (X²)`.
example (φ : (W (Fin 1) ⧸ Ideal.span {washnitzerAlgebra.X (Fin 1) K 0 ^ 2}) →ₐ[K]
    (W (Fin 1) ⧸ Ideal.span {washnitzerAlgebra.X (Fin 1) K 0 ^ 2})) :
    Continuous φ :=
  φ.continuous_washnitzerAlgebra_quotient

end Examples

end DaggerContinuity

end TauCeti.Dagger
