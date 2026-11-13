/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.PowerBounded
public import TauCeti.RingTheory.Dagger.DaggerAlgebra.Map
public import TauCeti.RingTheory.Dagger.DaggerAlgebra.ResidueNorm

import TauCeti.RingTheory.Dagger.DaggerAlgebra.FaithfullyFlat
import TauCeti.RingTheory.Dagger.QuotientCompletion
import TauCeti.RingTheory.Huber.Normed

/-!
# Automatic continuity and the canonical topology of dagger algebras

Let `K` be a complete nontrivially normed ultrametric field and `A` a `K`-dagger algebra. Equipping
`A` with the residue norm `TauCeti.Dagger.residueNormedCommRing` of its chosen minimal presentation
`W_n ↠ A` embeds `A` isometrically as a dense `K`-subalgebra of its affinoid completion
`Â = completion K A` (`TauCeti.Dagger.isometry_toCompletion`,
`TauCeti.Dagger.denseRange_toCompletion`). Combined with the universal property and functoriality of
`Â` (`TauCeti.Dagger.completionLift`, `TauCeti.Dagger.completionMap`), this yields the topological
theory of dagger algebras:

* **Automatic continuity** (`TauCeti.Dagger.washnitzerAlgebra.continuous_algHom_quotient`,
  `TauCeti.Dagger.continuous_algHom`): every `K`-algebra homomorphism `φ : A →ₐ[K] B` of dagger
  algebras (or between Monsky–Washnitzer presentation quotients `W_σ ⧸ I →ₐ[K] W_τ ⧸ J`) is
  continuous and norm-bounded, with no topological hypothesis on `φ`. Indeed `toCompletion K B ∘ φ`
  factors as `completionMap φ ∘ toCompletion K A`, where `completionMap φ` is continuous between
  affinoid completions and `toCompletion K B` is an isometry.
* **Canonical topology and presentation independence**
  (`TauCeti.Dagger.washnitzerAlgebra.presentationContinuousAlgEquiv`,
  `TauCeti.Dagger.presentationResidueContinuousAlgEquiv`, `TauCeti.Dagger.toContinuousAlgEquiv`):
  all Monsky–Washnitzer presentations `π : W_σ ↠ A` induce Lipschitz-equivalent residue norms and
  hence the same topology on `A`. Every surjective morphism `φ : A →ₐ[K] B` of dagger algebras is an
  open quotient map (`TauCeti.Dagger.isOpenQuotientMap_algHom`) inducing a topological `K`-algebra
  isomorphism `A ⧸ ker φ ≃A[K] B` (`TauCeti.Dagger.quotientKerContinuousAlgEquiv`), and every ideal
  of `A` is closed (`TauCeti.Dagger.isClosed_ideal_residueNormedCommRing`).
* **Power-bounded and topologically nilpotent elements**
  (`TauCeti.Dagger.IsDaggerAlgebra.isPowerBounded_iff_supSeminorm_le_one`,
  `TauCeti.Dagger.IsDaggerAlgebra.isTopologicallyNilpotent_iff_supSeminorm_lt_one`): in the
  canonical topology on `A`, the power-bounded elements are `{a | |a|sup ≤ 1}` and the topologically
  nilpotent elements are `{a | |a|sup < 1}`, both preserved by arbitrary `K`-algebra homomorphisms
  of dagger algebras.

## Main definitions

* `TauCeti.Dagger.washnitzerAlgebra.presentationContinuousAlgEquiv`: the canonical topological
  `K`-algebra isomorphism `(W_σ ⧸ ker π₁) ≃A[K] (W_τ ⧸ ker π₂)` between any two overconvergent
  presentations of the same `K`-algebra.
* `TauCeti.Dagger.residueContinuousAlgEquiv`,
  `TauCeti.Dagger.presentationResidueContinuousAlgEquiv`: topological `K`-algebra comparisons
  between `(A, residueNormedCommRing K A)` and `W_σ ⧸ ker π` for any presentation `π : W_σ ↠ A`.
* `TauCeti.Dagger.toContinuousAlgEquiv`: upgrades an algebraic isomorphism `A ≃ₐ[K] B` of dagger
  algebras to a topological `K`-algebra isomorphism `A ≃A[K] B`.
* `TauCeti.Dagger.quotientKerContinuousAlgEquiv`: the continuous first isomorphism theorem
  `(A ⧸ ker φ) ≃A[K] B` for a surjective morphism `φ : A →ₐ[K] B` of dagger algebras.

## Main results

* `TauCeti.Dagger.washnitzerAlgebra.continuous_algHom_quotient`,
  `TauCeti.Dagger.continuous_algHom`: automatic continuity of `K`-algebra homomorphisms between
  presentation quotients and between dagger algebras.
* `TauCeti.Dagger.washnitzerAlgebra.exists_pos_forall_norm_presentationContinuousAlgEquiv`:
  two-sided Lipschitz equivalence of residue norms from any two presentations.
* `TauCeti.Dagger.isClosed_ideal_residueNormedCommRing`,
  `TauCeti.Dagger.isOpenQuotientMap_algHom`: closedness of ideals and openness of surjective
  morphisms of dagger algebras.
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
  {σ τ : Type*} [Finite σ] [Finite τ]

local notation "W " α:max => washnitzerAlgebra α K
local notation "T " α:max => IsRestricted.subring (R := K) (fun _ : α ↦ (1 : ℝ))

/-- Every `K`-algebra homomorphism from a Monsky–Washnitzer presentation quotient `W_σ ⧸ I` into a
completely normed affinoid algebra is continuous for the quotient Gauss norm on `W_σ ⧸ I`. -/
theorem continuous_algHom_quotient_of_isAffinoidAlgebra {S : Type*} [NormedCommRing S]
    [NormedAlgebra K S] [IsUltrametricDist S] [CompleteSpace S] (hS : IsAffinoidAlgebra K S)
    {I : Ideal (W σ)} (φ : (W σ ⧸ I) →ₐ[K] S) : Continuous φ := by
  let liftT : T σ →ₐ[K] S := liftToTate hS (φ.comp (Ideal.Quotient.mkₐ K I))
  have hker : I.map (toTate σ K) ≤ RingHom.ker liftT :=
    Ideal.map_le_iff_le_comap.mpr fun f hf ↦ by
      rw [Ideal.mem_comap, RingHom.mem_ker, liftToTate_toTate, AlgHom.comp_apply,
        Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hf, map_zero]
  let Φ : (T σ ⧸ I.map (toTate σ K)) →ₐ[K] S :=
    Ideal.Quotient.liftₐ _ liftT fun _ hx ↦ RingHom.mem_ker.mp (hker hx)
  let ι : (W σ ⧸ I) →ₐ[K] T σ ⧸ I.map (toTate σ K) :=
    Ideal.quotientMapₐ (I.map (toTate σ K)) (toTate σ K) Ideal.le_comap_map
  have hcomp : (Φ : _ → S) ∘ ι = φ := by
    ext x
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (Ideal.Quotient.lift_mk _ _ _).trans (liftToTate_toTate hS _ f)
  have := ((isAffinoidAlgebra_tate (K := K) (σ := σ)).quotient
    (I.map (toTate σ K))).isNoetherianRing
  rw [← hcomp]
  exact (IsAffinoidAlgebra.continuous_algHom (K := K) (A := S)
    (B := T σ ⧸ I.map (toTate σ K)) hS Φ).comp I.isometry_quotientMap_toTate.continuous

/-- **Automatic continuity on presentation quotients.** Every `K`-algebra homomorphism between
Monsky–Washnitzer presentation quotients is continuous for their quotient Gauss norms. -/
theorem continuous_algHom_quotient {I : Ideal (W σ)} {J : Ideal (W τ)}
    (φ : (W σ ⧸ I) →ₐ[K] (W τ ⧸ J)) : Continuous φ := by
  let ιJ : (W τ ⧸ J) →ₐ[K] T τ ⧸ J.map (toTate τ K) :=
    Ideal.quotientMapₐ (J.map (toTate τ K)) (toTate τ K) Ideal.le_comap_map
  refine J.isometry_quotientMap_toTate.isEmbedding.isInducing.continuous_iff.mpr ?_
  rw [← AlgHom.coe_comp]
  exact continuous_algHom_quotient_of_isAffinoidAlgebra (K := K) (σ := σ)
    (S := T τ ⧸ J.map (toTate τ K)) (I := I)
    ((isAffinoidAlgebra_tate (K := K) (σ := τ)).quotient (J.map (toTate τ K)))
    (ιJ.comp φ)

/-- Every `K`-algebra homomorphism between Monsky–Washnitzer presentation quotients is bounded for
their quotient Gauss norms. -/
theorem exists_pos_forall_norm_map_quotient_le {I : Ideal (W σ)} {J : Ideal (W τ)}
    (φ : (W σ ⧸ I) →ₐ[K] (W τ ⧸ J)) :
    ∃ C > 0, ∀ x : W σ ⧸ I, ‖φ x‖ ≤ C * ‖x‖ :=
  (⟨φ.toLinearMap, continuous_algHom_quotient φ⟩ : (W σ ⧸ I) →L[K] (W τ ⧸ J)).bound

/-- Every `K`-algebra isomorphism between Monsky–Washnitzer presentation quotients is a topological
`K`-algebra isomorphism for their quotient Gauss norms. -/
noncomputable def quotientContinuousAlgEquivOfAlgEquiv {I : Ideal (W σ)} {J : Ideal (W τ)}
    (e : (W σ ⧸ I) ≃ₐ[K] (W τ ⧸ J)) : (W σ ⧸ I) ≃A[K] (W τ ⧸ J) :=
  { e with
    continuous_toFun := continuous_algHom_quotient e.toAlgHom
    continuous_invFun := continuous_algHom_quotient e.symm.toAlgHom }

/-- `quotientContinuousAlgEquivOfAlgEquiv e` has the same underlying function as `e`. -/
@[simp]
theorem coe_quotientContinuousAlgEquivOfAlgEquiv {I : Ideal (W σ)} {J : Ideal (W τ)}
    (e : (W σ ⧸ I) ≃ₐ[K] (W τ ⧸ J)) :
    ⇑(quotientContinuousAlgEquivOfAlgEquiv e) = ⇑e := (rfl)

/-- The underlying `AlgEquiv` of `quotientContinuousAlgEquivOfAlgEquiv e` is `e`. -/
@[simp]
theorem toAlgEquiv_quotientContinuousAlgEquivOfAlgEquiv {I : Ideal (W σ)} {J : Ideal (W τ)}
    (e : (W σ ⧸ I) ≃ₐ[K] (W τ ⧸ J)) :
    (quotientContinuousAlgEquivOfAlgEquiv e).toAlgEquiv = e := (rfl)

/-- **Presentation independence of the residue-norm topology.** Two Monsky–Washnitzer presentations
`π₁ : W_σ ↠ C` and `π₂ : W_τ ↠ C` of the same `K`-algebra give residue algebras whose quotient Gauss
norms define the same topology: the canonical `K`-algebra isomorphism compatible with both
presentations is a homeomorphism. -/
noncomputable def presentationContinuousAlgEquiv {C : Type*} [CommRing C] [Algebra K C]
    (π₁ : W σ →ₐ[K] C) (hπ₁ : Function.Surjective π₁)
    (π₂ : W τ →ₐ[K] C) (hπ₂ : Function.Surjective π₂) :
    (W σ ⧸ RingHom.ker π₁) ≃A[K] (W τ ⧸ RingHom.ker π₂) :=
  quotientContinuousAlgEquivOfAlgEquiv
    ((Ideal.quotientKerAlgEquivOfSurjective hπ₁).trans
      (Ideal.quotientKerAlgEquivOfSurjective hπ₂).symm)

/-- `presentationContinuousAlgEquiv` is compatible with both presentations via
`Ideal.kerLiftAlg`. -/
@[simp]
theorem kerLiftAlg_presentationContinuousAlgEquiv {C : Type*} [CommRing C] [Algebra K C]
    (π₁ : W σ →ₐ[K] C) (hπ₁ : Function.Surjective π₁)
    (π₂ : W τ →ₐ[K] C) (hπ₂ : Function.Surjective π₂) (x : W σ ⧸ RingHom.ker π₁) :
    Ideal.kerLiftAlg π₂ (presentationContinuousAlgEquiv π₁ hπ₁ π₂ hπ₂ x) =
      Ideal.kerLiftAlg π₁ x := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨g, hg⟩ := hπ₂ (π₁ f)
  have hsymm : (Ideal.quotientKerAlgEquivOfSurjective hπ₂).symm (π₁ f) =
      Ideal.Quotient.mk _ g :=
    (Ideal.quotientKerAlgEquivOfSurjective hπ₂).symm_apply_eq.mpr
      ((Ideal.quotientKerAlgEquivOfSurjective_mk hπ₂ g).trans hg).symm
  simp [presentationContinuousAlgEquiv, hsymm, hg]

/-- **Equivalence of residue norms across presentations.** For any two Monsky–Washnitzer
presentations of the same `K`-algebra, the induced quotient Gauss norms bound each other up to
positive multiplicative constants. -/
theorem exists_pos_forall_norm_presentationContinuousAlgEquiv {C : Type*} [CommRing C]
    [Algebra K C] (π₁ : W σ →ₐ[K] C) (hπ₁ : Function.Surjective π₁)
    (π₂ : W τ →ₐ[K] C) (hπ₂ : Function.Surjective π₂) :
    ∃ c > 0, ∃ C' > 0, ∀ x : W σ ⧸ RingHom.ker π₁,
      c * ‖x‖ ≤ ‖presentationContinuousAlgEquiv π₁ hπ₁ π₂ hπ₂ x‖ ∧
        ‖presentationContinuousAlgEquiv π₁ hπ₁ π₂ hπ₂ x‖ ≤ C' * ‖x‖ := by
  let e := (Ideal.quotientKerAlgEquivOfSurjective hπ₁).trans
    (Ideal.quotientKerAlgEquivOfSurjective hπ₂).symm
  obtain ⟨C₁, hC₁, hle₁⟩ := exists_pos_forall_norm_map_quotient_le e.toAlgHom
  obtain ⟨C₂, hC₂, hle₂⟩ := exists_pos_forall_norm_map_quotient_le e.symm.toAlgHom
  refine ⟨C₂⁻¹, inv_pos.mpr hC₂, C₁, hC₁, fun x ↦ ⟨?_, hle₁ x⟩⟩
  rw [inv_mul_le_iff₀ hC₂]
  simpa [presentationContinuousAlgEquiv, e] using hle₂ (e x)

/-- On a Monsky–Washnitzer presentation quotient `W_σ ⧸ I`, the supremum seminorm is bounded by the
quotient Gauss norm. -/
theorem supSeminorm_quotient_le_norm {I : Ideal (W σ)} (x : W σ ⧸ I) :
    supSeminorm K x ≤ ‖x‖ := by
  obtain ⟨f, rfl, hf⟩ := I.exists_mk_eq_and_norm_eq_washnitzerAlgebra x
  exact (supSeminorm_map_le_norm (φ := Ideal.Quotient.mkₐ K I)
    Ideal.Quotient.mk_surjective f).trans_eq hf

end washnitzerAlgebra

end PresentationQuotients

section DaggerTopology

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

section ResidueEquiv

variable (K) (A : Type*) [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]

/-- The residue isomorphism `residueAlgEquiv K A : A ≃ₐ[K] W_n ⧸ ker (presentation K A)` as a
topological `K`-algebra isomorphism for `residueNormedCommRing K A`. -/
noncomputable def residueContinuousAlgEquiv :
    letI := residueNormedCommRing K A
    A ≃A[K] washnitzerAlgebra (Fin (presentationDim K A)) K ⧸
      RingHom.ker (presentation K A) :=
  letI := residueNormedCommRing K A
  have hiso : Isometry (residueAlgEquiv K A) :=
    (AddMonoidHomClass.isometry_iff_norm (residueAlgEquiv K A)).mpr (norm_residueAlgEquiv K A)
  have hiso_symm : Isometry (residueAlgEquiv K A).symm :=
    (AddMonoidHomClass.isometry_iff_norm (residueAlgEquiv K A).symm).mpr fun x ↦
      (norm_residueAlgEquiv K A ((residueAlgEquiv K A).symm x)).symm.trans
        (congrArg norm ((residueAlgEquiv K A).apply_symm_apply x))
  { residueAlgEquiv K A with
    continuous_toFun := hiso.continuous
    continuous_invFun := hiso_symm.continuous }

/-- `residueContinuousAlgEquiv` has the same underlying function as `residueAlgEquiv`. -/
@[simp↓]
theorem coe_residueContinuousAlgEquiv :
    letI := residueNormedCommRing K A
    ⇑(residueContinuousAlgEquiv K A) = ⇑(residueAlgEquiv K A) :=
  letI := residueNormedCommRing K A
  (rfl)

/-- The underlying `AlgEquiv` of `residueContinuousAlgEquiv` is `residueAlgEquiv`. -/
@[simp↓]
theorem toAlgEquiv_residueContinuousAlgEquiv :
    letI := residueNormedCommRing K A
    (residueContinuousAlgEquiv K A).toAlgEquiv = residueAlgEquiv K A :=
  letI := residueNormedCommRing K A
  (rfl)

/-- `residueContinuousAlgEquiv` sends `presentation K A f` to the quotient class of `f`. -/
@[simp↓]
theorem residueContinuousAlgEquiv_presentation
    (f : washnitzerAlgebra (Fin (presentationDim K A)) K) :
    letI := residueNormedCommRing K A
    residueContinuousAlgEquiv K A (presentation K A f) = Ideal.Quotient.mk _ f :=
  letI := residueNormedCommRing K A
  residueAlgEquiv_presentation K A f

end ResidueEquiv

section Morphisms

variable {A B : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
  [CommRing B] [Algebra K B] [IsDaggerAlgebra K B]

/-- Every `K`-algebra homomorphism from a dagger algebra (with its residue norm) into a completely
normed affinoid algebra is continuous. -/
theorem continuous_algHom_of_isAffinoidAlgebra {S : Type*} [NormedCommRing S] [NormedAlgebra K S]
    [IsUltrametricDist S] [CompleteSpace S] (hS : IsAffinoidAlgebra K S) (φ : A →ₐ[K] S) :
    letI := residueNormedCommRing K A
    Continuous φ := by
  let := residueNormedCommRing K A
  have := (isAffinoidAlgebra_completion (K := K) (A := A)).isNoetherianRing
  have hcomp : (completionLift hS φ : completion K A → S) ∘ toCompletion K A = φ :=
    funext (completionLift_toCompletion hS φ)
  rw [← hcomp]
  exact (IsAffinoidAlgebra.continuous_algHom (K := K) (A := S) (B := completion K A) hS
    (completionLift hS φ)).comp (isometry_toCompletion K A).continuous

/-- **Automatic continuity for dagger algebras.** Every `K`-algebra homomorphism `φ : A →ₐ[K] B`
between dagger algebras is continuous for their residue norms, with no continuity hypothesis on `φ`
or on any presentation. -/
theorem continuous_algHom (φ : A →ₐ[K] B) :
    letI := residueNormedCommRing K A
    letI := residueNormedCommRing K B
    Continuous φ := by
  let := residueNormedCommRing K A
  let := residueNormedCommRing K B
  refine (isometry_toCompletion K B).isEmbedding.isInducing.continuous_iff.mpr ?_
  have hcomp : (toCompletion K B : B → completion K B) ∘ φ =
      completionMap φ ∘ toCompletion K A :=
    funext fun a ↦ (completionMap_toCompletion φ a).symm
  rw [hcomp]
  exact (continuous_completionMap φ).comp (isometry_toCompletion K A).continuous

/-- Every `K`-algebra homomorphism `φ : A →ₐ[K] B` of dagger algebras is norm-bounded for their
residue norms. -/
theorem exists_pos_forall_norm_algHom_le (φ : A →ₐ[K] B) :
    letI := residueNormedCommRing K A
    letI := residueNormedCommRing K B
    ∃ C > 0, ∀ a : A, ‖φ a‖ ≤ C * ‖a‖ := by
  let := residueNormedCommRing K A
  let := residueNormedAlgebra K A
  let := residueNormedCommRing K B
  let := residueNormedAlgebra K B
  exact (⟨φ.toLinearMap, continuous_algHom φ⟩ : A →L[K] B).bound

/-- **Uniqueness of the dagger topology.** Every `K`-algebra isomorphism `e : A ≃ₐ[K] B` between
dagger algebras is a homeomorphism for their residue norms. -/
noncomputable def toContinuousAlgEquiv (e : A ≃ₐ[K] B) :
    letI := residueNormedCommRing K A
    letI := residueNormedCommRing K B
    A ≃A[K] B :=
  letI := residueNormedCommRing K A
  letI := residueNormedCommRing K B
  { e with
    continuous_toFun := continuous_algHom e.toAlgHom
    continuous_invFun := continuous_algHom e.symm.toAlgHom }

/-- `toContinuousAlgEquiv e` has the same underlying function as `e`. -/
@[simp↓]
theorem coe_toContinuousAlgEquiv (e : A ≃ₐ[K] B) :
    letI := residueNormedCommRing K A
    letI := residueNormedCommRing K B
    ⇑(toContinuousAlgEquiv e) = ⇑e :=
  letI := residueNormedCommRing K A
  letI := residueNormedCommRing K B
  (rfl)

/-- The underlying `AlgEquiv` of `toContinuousAlgEquiv e` is `e`. -/
@[simp↓]
theorem toAlgEquiv_toContinuousAlgEquiv (e : A ≃ₐ[K] B) :
    letI := residueNormedCommRing K A
    letI := residueNormedCommRing K B
    (toContinuousAlgEquiv e).toAlgEquiv = e :=
  letI := residueNormedCommRing K A
  letI := residueNormedCommRing K B
  (rfl)

/-- `toContinuousAlgEquiv` commutes with `.symm`. -/
@[simp↓]
theorem toContinuousAlgEquiv_symm (e : A ≃ₐ[K] B) :
    letI := residueNormedCommRing K A
    letI := residueNormedCommRing K B
    (toContinuousAlgEquiv e).symm = toContinuousAlgEquiv e.symm := by
  let := residueNormedCommRing K A
  let := residueNormedCommRing K B
  ext b
  exact rfl

/-- For any surjective presentation `π : W_σ →ₐ[K] A` of a dagger algebra, the first isomorphism
theorem `(W_σ ⧸ ker π) ≃ₐ[K] A` is a topological `K`-algebra isomorphism between the quotient Gauss
norm of `π` and `residueNormedCommRing K A`. -/
noncomputable def presentationResidueContinuousAlgEquiv {σ : Type*} [Finite σ]
    (π : washnitzerAlgebra σ K →ₐ[K] A) (hπ : Function.Surjective π) :
    letI := residueNormedCommRing K A
    (washnitzerAlgebra σ K ⧸ RingHom.ker π) ≃A[K] A :=
  letI := residueNormedCommRing K A
  (washnitzerAlgebra.presentationContinuousAlgEquiv π hπ
    (presentation K A) (presentation_surjective K A)).trans
    (residueContinuousAlgEquiv K A).symm

/-- `presentationResidueContinuousAlgEquiv π hπ` sends the class of `f` to `π f`. -/
@[simp↓]
theorem presentationResidueContinuousAlgEquiv_mk {σ : Type*} [Finite σ]
    (π : washnitzerAlgebra σ K →ₐ[K] A) (hπ : Function.Surjective π)
    (f : washnitzerAlgebra σ K) :
    letI := residueNormedCommRing K A
    presentationResidueContinuousAlgEquiv π hπ (Ideal.Quotient.mk _ f) = π f := by
  let := residueNormedCommRing K A
  obtain ⟨g, hg⟩ := presentation_surjective K A (π f)
  have hmk : washnitzerAlgebra.presentationContinuousAlgEquiv π hπ
      (presentation K A) (presentation_surjective K A) (Ideal.Quotient.mk _ f) =
      Ideal.Quotient.mk _ g := by
    have hsymm : (Ideal.quotientKerAlgEquivOfSurjective (presentation_surjective K A)).symm
        (π f) = Ideal.Quotient.mk _ g :=
      (Ideal.quotientKerAlgEquivOfSurjective (presentation_surjective K A)).symm_apply_eq.mpr
        ((Ideal.quotientKerAlgEquivOfSurjective_mk (presentation_surjective K A) g).trans hg).symm
    simp [washnitzerAlgebra.presentationContinuousAlgEquiv, hsymm]
  have hsymm : (residueContinuousAlgEquiv K A).symm (Ideal.Quotient.mk _ g) =
      presentation K A g :=
    (residueContinuousAlgEquiv K A).symm_apply_eq.mpr
      (residueContinuousAlgEquiv_presentation K A g).symm
  simp [presentationResidueContinuousAlgEquiv, hmk, hsymm, hg]

/-- Every surjective `K`-algebra homomorphism `π : W_σ →ₐ[K] A` from a Monsky–Washnitzer algebra
onto a dagger algebra is an open quotient map for the Gauss norm on `W_σ` and the residue norm on
`A`. -/
theorem isOpenQuotientMap_of_surjective_washnitzerAlgebra {σ : Type*} [Finite σ]
    (π : washnitzerAlgebra σ K →ₐ[K] A) (hπ : Function.Surjective π) :
    letI := residueNormedCommRing K A
    IsOpenQuotientMap π := by
  let := residueNormedCommRing K A
  let e := presentationResidueContinuousAlgEquiv π hπ
  have he : IsOpenQuotientMap e := ⟨e.surjective, e.continuous, e.isOpenMap⟩
  have hcomp : (e : _ → A) ∘ Ideal.Quotient.mk (RingHom.ker π) = π :=
    funext (presentationResidueContinuousAlgEquiv_mk π hπ)
  rw [← hcomp]
  exact he.comp (QuotientRing.isOpenQuotientMap_mk (RingHom.ker π))

/-- The chosen minimal presentation `presentation K A : W_n →ₐ[K] A` is an open quotient map onto
`(A, residueNormedCommRing K A)`. -/
theorem isOpenQuotientMap_presentation (K A : Type*) [NontriviallyNormedField K]
    [IsUltrametricDist K] [CompleteSpace K] [CommRing A] [Algebra K A] [IsDaggerAlgebra K A] :
    letI := residueNormedCommRing K A
    IsOpenQuotientMap (presentation K A) :=
  isOpenQuotientMap_of_surjective_washnitzerAlgebra (presentation K A) (presentation_surjective K A)

/-- **Every ideal of a dagger algebra is closed** in its canonical residue-norm topology. -/
theorem isClosed_ideal_residueNormedCommRing (J : Ideal A) :
    letI := residueNormedCommRing K A
    IsClosed (J : Set A) := by
  let := residueNormedCommRing K A
  have hc : IsClosed (J.map (toCompletion K A) : Set (completion K A)) :=
    IsAffinoidAlgebra.isClosed_ideal (K := K) (A := completion K A) isAffinoidAlgebra_completion _
  have hpre : (toCompletion K A) ⁻¹' (J.map (toCompletion K A) : Set (completion K A)) = J := by
    rw [← Ideal.coe_comap, comap_map_toCompletion K J]
  exact hpre ▸ hc.preimage (isometry_toCompletion K A).continuous

/-- **Surjective morphisms of dagger algebras are open quotient maps.** Every surjective `K`-algebra
homomorphism `φ : A →ₐ[K] B` between dagger algebras is an open quotient map for their residue
norms, so `B` carries the quotient topology induced by `φ`. -/
theorem isOpenQuotientMap_algHom (φ : A →ₐ[K] B) (hφ : Function.Surjective φ) :
    letI := residueNormedCommRing K A
    letI := residueNormedCommRing K B
    IsOpenQuotientMap φ := by
  let := residueNormedCommRing K A
  let := residueNormedCommRing K B
  rw [← (isOpenQuotientMap_presentation K A).of_comp_iff]
  exact isOpenQuotientMap_of_surjective_washnitzerAlgebra (φ.comp (presentation K A))
    (hφ.comp (presentation_surjective K A))

/-- **The continuous first isomorphism theorem for dagger algebras.** For a surjective `K`-algebra
homomorphism `φ : A →ₐ[K] B` of dagger algebras, the algebraic isomorphism `A ⧸ ker φ ≃ₐ[K] B` is a
homeomorphism for the quotient topology of `residueNormedCommRing K A` and
`residueNormedCommRing K B`. -/
noncomputable def quotientKerContinuousAlgEquiv (φ : A →ₐ[K] B) (hφ : Function.Surjective φ) :
    letI := residueNormedCommRing K A
    letI := residueNormedCommRing K B
    (A ⧸ RingHom.ker φ) ≃A[K] B :=
  letI := residueNormedCommRing K A
  letI := residueNormedCommRing K B
  let e := Ideal.quotientKerAlgEquivOfSurjective hφ
  have hmk : IsOpenQuotientMap (Ideal.Quotient.mk (RingHom.ker φ)) :=
    QuotientRing.isOpenQuotientMap_mk (RingHom.ker φ)
  have hφo : IsOpenQuotientMap φ := isOpenQuotientMap_algHom φ hφ
  { e with
    continuous_toFun := hmk.continuous_comp_iff.mp <| by
      have hcomp : e.toFun ∘ Ideal.Quotient.mk (RingHom.ker φ) = φ :=
        funext (Ideal.quotientKerAlgEquivOfSurjective_mk hφ)
      rw [hcomp]
      exact hφo.continuous
    continuous_invFun := hφo.continuous_comp_iff.mp <| by
      have hcomp : e.invFun ∘ φ = Ideal.Quotient.mk (RingHom.ker φ) :=
        funext fun a ↦ e.symm_apply_eq.mpr (Ideal.quotientKerAlgEquivOfSurjective_mk hφ a).symm
      rw [hcomp]
      exact continuous_quot_mk }

/-- `quotientKerContinuousAlgEquiv φ hφ` sends the class of `a` to `φ a`. -/
@[simp↓]
theorem quotientKerContinuousAlgEquiv_mk (φ : A →ₐ[K] B) (hφ : Function.Surjective φ) (a : A) :
    letI := residueNormedCommRing K A
    letI := residueNormedCommRing K B
    quotientKerContinuousAlgEquiv φ hφ (Ideal.Quotient.mk _ a) = φ a :=
  letI := residueNormedCommRing K A
  letI := residueNormedCommRing K B
  Ideal.quotientKerAlgEquivOfSurjective_mk hφ a

/-- The underlying `AlgEquiv` of `quotientKerContinuousAlgEquiv φ hφ` is
`Ideal.quotientKerAlgEquivOfSurjective hφ`. -/
@[simp↓]
theorem toAlgEquiv_quotientKerContinuousAlgEquiv (φ : A →ₐ[K] B) (hφ : Function.Surjective φ) :
    letI := residueNormedCommRing K A
    letI := residueNormedCommRing K B
    (quotientKerContinuousAlgEquiv φ hφ).toAlgEquiv =
      Ideal.quotientKerAlgEquivOfSurjective hφ :=
  letI := residueNormedCommRing K A
  letI := residueNormedCommRing K B
  (rfl)

end Morphisms

end DaggerTopology

section PowerBounded

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
  [CommRing B] [Algebra K B] [IsDaggerAlgebra K B]

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
  obtain ⟨f, rfl, hf⟩ := exists_presentation_norm_eq K A a
  exact (washnitzerAlgebra.supSeminorm_map_le_norm (presentation_surjective K A) f).trans_eq hf

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

/-- Every `K`-algebra homomorphism `φ : A →ₐ[K] B` of dagger algebras maps power-bounded elements to
power-bounded elements. -/
theorem isPowerBounded_map (φ : A →ₐ[K] B) {a : A} :
    letI := residueNormedCommRing K A
    letI := residueNormedCommRing K B
    Huber.IsPowerBounded a → Huber.IsPowerBounded (φ a) :=
  letI := residueNormedCommRing K A
  letI := residueNormedCommRing K B
  fun ha ↦ (isPowerBounded_iff_supSeminorm_le_one (K := K) (a := φ a)).mpr <|
    (supSeminorm_map_le φ a).trans
      ((isPowerBounded_iff_supSeminorm_le_one (K := K) (a := a)).mp ha)

/-- Every `K`-algebra homomorphism `φ : A →ₐ[K] B` of dagger algebras maps topologically nilpotent
elements to topologically nilpotent elements. -/
theorem isTopologicallyNilpotent_map (φ : A →ₐ[K] B) {a : A} :
    letI := residueNormedCommRing K A
    letI := residueNormedCommRing K B
    IsTopologicallyNilpotent a → IsTopologicallyNilpotent (φ a) :=
  letI := residueNormedCommRing K A
  letI := residueNormedCommRing K B
  fun ha ↦ (isTopologicallyNilpotent_iff_supSeminorm_lt_one (K := K) (a := φ a)).mpr <|
    (supSeminorm_map_le φ a).trans_lt
      ((isTopologicallyNilpotent_iff_supSeminorm_lt_one (K := K) (a := a)).mp ha)

end IsDaggerAlgebra

end PowerBounded

end TauCeti.Dagger
