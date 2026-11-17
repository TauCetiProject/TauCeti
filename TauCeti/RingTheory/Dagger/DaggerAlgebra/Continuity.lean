/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.DaggerAlgebra.Map
public import TauCeti.RingTheory.Dagger.DaggerAlgebra.ResidueNorm

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
  simpa only [supSeminorm_algEquiv, norm_residueAlgEquiv] using
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
