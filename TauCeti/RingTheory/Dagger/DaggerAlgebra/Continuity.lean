/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Algebra.Equiv
public import TauCeti.RingTheory.Affinoid.PowerBounded
public import TauCeti.RingTheory.Dagger.DaggerAlgebra.ResidueNorm
public import TauCeti.RingTheory.Dagger.SupSeminorm

import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import TauCeti.RingTheory.Affinoid.Continuity
import TauCeti.RingTheory.Affinoid.Restricted
import TauCeti.RingTheory.Dagger.QuotientCompletion
import TauCeti.RingTheory.Huber.Normed
import TauCeti.RingTheory.Ideal.KrullIntersection

/-!
# Automatic continuity, norm equivalence, and completion functoriality for dagger algebras

Let `K` be a complete nontrivially normed ultrametric field. Every `K`-dagger algebra `A` has an
affinoid completion `τ : A → Â` (`TauCeti.Dagger.toCompletion`), isometric with dense image for
the residue norm of the chosen minimal presentation (`TauCeti.Dagger.isometry_toCompletion`,
`TauCeti.Dagger.denseRange_toCompletion`). Because the Monsky–Washnitzer algebra `W_n` is not
complete in positive dimension (`TauCeti.Dagger.washnitzerAlgebra.not_completeSpace`), the closed
graph theorem cannot be applied directly between presentation quotients `W_n ⧸ I`.

Following Grosse-Klönne, one first proves that every `K`-algebra homomorphism `χ : W_σ → C` into a
completely normed `K`-affinoid algebra extends uniquely along `W_σ → T_σ` to `ψ : T_σ → C`:

1. Every ideal of `W_σ` is closed for the Gauss norm (`washnitzerAlgebra.isClosed_ideal`), so any
   `K`-algebra homomorphism from `W_σ` into a finite-dimensional topological `K`-algebra is
   continuous (`washnitzerAlgebra.continuous_algHom_of_finiteDimensional`).
2. Pullback of classical points shows `|χ(f)(x)| ≤ ‖f‖`, sending the Gauss unit ball of `W_σ` into
   `C°` (`washnitzerAlgebra.isPowerBounded_map_of_isAffinoidAlgebra`). The universal property of
   `T_σ` (`TauCeti.IsAffinoidAlgebra.restrictedLift`) produces a continuous map `ψ : T_σ → C`
   agreeing with `χ` on polynomials.
3. Modulo every `𝔪^k` (`𝔪` maximal in `C`), `C ⧸ 𝔪^k` is finite-dimensional and Hausdorff, so `χ`
   and `ψ ∘ toTate` are continuous and agree on dense polynomials; Krull's intersection theorem in
   `C` gives `ψ ∘ toTate = χ`.

This yields the universal property of `toCompletion K A : A → Â` for arbitrary completely normed
affinoid targets (`TauCeti.Dagger.completionLift`, `TauCeti.Dagger.eq_completionLift`), making
completion functorial (`TauCeti.Dagger.completionMap`), identifying `T_σ ⧸ (ker π) T_σ` with
`completion K A` for any presentation `π : W_σ ↠ A` (`TauCeti.Dagger.presentationCompletionEquiv`),
and reducing continuity, uniform continuity, Lipschitz bounds, and power-boundedness preservation
for arbitrary `K`-algebra homomorphisms of dagger algebras to automatic continuity for affinoid
algebras (`TauCeti.IsAffinoidAlgebra.continuous_algHom`). In particular, all Monsky–Washnitzer
presentations of `A` induce equivalent residue norms and the same uniformity.

## Main definitions

* `TauCeti.Dagger.washnitzerAlgebra.tateLift` and `tateQuotientLift`: the unique extension of
  `W_σ →ₐ[K] C` to `T_σ →ₐ[K] C` (and to `T_σ ⧸ I T_σ →ₐ[K] C`) for an affinoid target `C`.
* `TauCeti.Dagger.completionLift`: the unique extension of `A →ₐ[K] C` to `completion K A →ₐ[K] C`
  for a completely normed affinoid target `C`.
* `TauCeti.Dagger.completionMap` and `TauCeti.Dagger.completionContinuousAlgEquiv`: functoriality
  `φ ↦ φ̂` of affinoid completions on `K`-algebra homomorphisms and isomorphisms.
* `TauCeti.Dagger.presentationCompletionEquiv`, `TauCeti.Dagger.completionWashnitzerEquiv`, and
  `TauCeti.Dagger.completionQuotientEquiv`: presentation-independence `T_σ ⧸ (ker π) T_σ ≃A[K] Â`.
* `TauCeti.Dagger.presentationContinuousAlgEquiv`: topological algebra isomorphism between residue
  algebras of any two Monsky–Washnitzer presentations.

## Main results

* `TauCeti.Dagger.washnitzerAlgebra.continuous_algHom_of_isAffinoidAlgebra`: automatic continuity
  from `W_σ` into completely normed affinoid algebras.
* `TauCeti.Dagger.eq_completionLift` and `TauCeti.Dagger.eq_completionMap`: uniqueness of
  extensions along `toCompletion K A` with no continuity assumption.
* `TauCeti.Dagger.IsDaggerAlgebra.continuous_algHom_of_isAffinoidAlgebra`,
  `TauCeti.Dagger.IsDaggerAlgebra.continuous_algHom_of_isInducing`,
  `TauCeti.Dagger.IsDaggerAlgebra.uniformContinuous_algHom_of_isInducing`,
  `TauCeti.Dagger.IsDaggerAlgebra.continuous_algHom`,
  `TauCeti.Dagger.IsDaggerAlgebra.exists_norm_map_le`, and
  `TauCeti.Dagger.IsDaggerAlgebra.isPowerBounded_map_of_isAffinoidAlgebra`: automatic continuity,
  uniform continuity, Lipschitz bounds, and power-boundedness preservation for `K`-algebra
  homomorphisms of dagger algebras.
* `TauCeti.Dagger.exists_mul_norm_le_and_norm_le_mul_quotientKerAlgEquivOfSurjective_symm` and
  `TauCeti.Dagger.induced_quotientKerAlgEquivOfSurjective_symm_toUniformSpace`: equivalence of
  presentation residue norms and equality of induced uniformities.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1, Proposition 1.6 and Theorem 1.7 (1).
* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert],
  §§3.7.5 and 6.1.3.
-/

public section

open Filter Topology _root_.MvPowerSeries

namespace TauCeti.Dagger

section WashnitzerAutomaticContinuity

namespace washnitzerAlgebra

variable {K σ τ : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Finite σ] [Finite τ]

local notation "W " α:max => washnitzerAlgebra α K
local notation "T " α:max => IsRestricted.subring (R := K) (fun _ : α ↦ (1 : ℝ))

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

section AffinoidTarget

variable {C : Type*} [NormedCommRing C] [NormedAlgebra K C] [IsUltrametricDist C] [CompleteSpace C]

/-- Any `K`-algebra homomorphism from `W_σ` into a completely normed affinoid algebra maps
elements of Gauss norm at most one to power-bounded elements. -/
theorem isPowerBounded_map_of_norm_le_one (hC : IsAffinoidAlgebra K C) (χ : W σ →ₐ[K] C)
    {f : W σ} (hf : ‖f‖ ≤ 1) : Huber.IsPowerBounded (χ f) := by
  rw [hC.isPowerBounded_iff_forall_pointNorm_le_one]
  intro x
  rw [← hC.pointNorm_maximalSpectrumComap χ x]
  exact (pointNorm_le_norm _ f).trans hf

/-- Any `K`-algebra homomorphism from `W_σ` into a completely normed affinoid algebra preserves
power-boundedness, without assuming continuity. -/
theorem isPowerBounded_map_of_isAffinoidAlgebra (hC : IsAffinoidAlgebra K C) (χ : W σ →ₐ[K] C)
    {f : W σ} (hf : Huber.IsPowerBounded f) : Huber.IsPowerBounded (χ f) :=
  isPowerBounded_map_of_norm_le_one hC χ (isPowerBounded_iff_norm_le_one.mp hf)

private theorem restrictedLift_comp_toTate {n : ℕ} (hC : IsAffinoidAlgebra K C)
    (χ : W (Fin n) →ₐ[K] C) :
    (isAffinoidAlgebra_self.restrictedLift hC (Algebra.ofId K C)
      (fun i ↦ isPowerBounded_map_of_norm_le_one hC χ (norm_X i).le)).comp
        (toTate (Fin n) K) = χ := by
  let ψ := isAffinoidAlgebra_self.restrictedLift hC (Algebra.ofId K C)
    (fun i ↦ isPowerBounded_map_of_norm_le_one hC χ (norm_X i).le)
  have := hC.isNoetherianRing
  have := (isAffinoidAlgebra_tate (K := K) (σ := Fin n)).isNoetherianRing
  have hpoly : (ψ.comp (toTate (Fin n) K)).comp (ofMvPolynomial (Fin n) K) =
      χ.comp (ofMvPolynomial (Fin n) K) := by
    apply MvPolynomial.algHom_ext
    intro i
    have hX : toTate (Fin n) K (X (Fin n) K i) =
        ⟨_root_.MvPowerSeries.X i, isRestricted_X _ i⟩ := Subtype.ext (by simp)
    simp [ψ, hX]
  ext f
  suffices ψ (toTate (Fin n) K f) - χ f ∈ (⊥ : Ideal C) from sub_eq_zero.mp this
  rw [← Ideal.iInf_isMaximal_pow_eq_bot]
  simp only [Ideal.mem_iInf]
  intro m hm k _
  let := hm
  let I := m ^ k
  have : IsClosed (I : Set C) := hC.isClosed_ideal I
  have : Module.Finite K (C ⧸ I) := hC.finite_quotient_pow m k
  let q : C →ₐ[K] C ⧸ I := Ideal.Quotient.mkₐ K I
  -- Modulo `m ^ k`, both maps from `W_{Fin n}` are continuous and agree on dense polynomials.
  have hcont₁ : Continuous (q.comp (ψ.comp (toTate (Fin n) K))) :=
    continuous_quot_mk.comp ((hC.continuous_algHom ψ).comp isometry_toTate.continuous)
  have hcont₂ : Continuous (q.comp χ) := continuous_algHom_of_finiteDimensional (q.comp χ)
  have heq : ⇑(q.comp (ψ.comp (toTate (Fin n) K))) = ⇑(q.comp χ) :=
    denseRange_ofMvPolynomial.equalizer hcont₁ hcont₂
      (funext fun p ↦ congrArg q (AlgHom.congr_fun hpoly p))
  exact Ideal.Quotient.eq_zero_iff_mem.mp (by
    simpa only [q, AlgHom.comp_apply, map_sub, Ideal.Quotient.mkₐ_eq_mk] using
      sub_eq_zero.mpr (congrFun heq f))

open scoped Classical in
/-- **Unique extension from `W_σ` to `T_σ` into an affinoid algebra.** Every `K`-algebra
homomorphism `χ : W_σ →ₐ[K] C` into a completely normed `K`-affinoid algebra extends along
`toTate σ K` to a `K`-algebra homomorphism `T_σ →ₐ[K] C`. -/
noncomputable def tateLift (hC : IsAffinoidAlgebra K C) (χ : W σ →ₐ[K] C) : T σ →ₐ[K] C :=
  let := Fintype.ofFinite σ
  let e := Fintype.equivFin σ
  let χ' := χ.comp (renameAlgEquiv e.symm).toAlgHom
  (isAffinoidAlgebra_self.restrictedLift hC (Algebra.ofId K C)
    (fun i ↦ isPowerBounded_map_of_norm_le_one hC χ' (norm_X i).le)).comp
    (IsRestricted.renameAlgEquiv e (fun _ ↦ (1 : ℝ))).toAlgHom

/-- `tateLift hC χ` is continuous. -/
theorem continuous_tateLift (hC : IsAffinoidAlgebra K C) (χ : W σ →ₐ[K] C) :
    Continuous (tateLift hC χ) :=
  have := (isAffinoidAlgebra_tate (K := K) (σ := σ)).isNoetherianRing
  IsAffinoidAlgebra.continuous_algHom (K := K) (A := C) (B := T σ) hC (tateLift hC χ)

/-- `tateLift hC χ` extends `χ` along `toTate`. -/
@[simp]
theorem tateLift_comp_toTate (hC : IsAffinoidAlgebra K C) (χ : W σ →ₐ[K] C) :
    (tateLift hC χ).comp (toTate σ K) = χ := by
  classical
  let := Fintype.ofFinite σ
  let e := Fintype.equivFin σ
  have hcomm (f : W σ) :
      IsRestricted.renameAlgEquiv e (fun _ ↦ (1 : ℝ)) (toTate σ K f) =
        toTate (Fin (Fintype.card σ)) K (renameAlgEquiv e f) := by
    ext t
    simp [coe_toTate]
  ext f
  have hf := AlgHom.congr_fun (restrictedLift_comp_toTate hC
    (χ.comp (renameAlgEquiv e.symm).toAlgHom)) (renameAlgEquiv e f)
  have hren : renameAlgEquiv e.symm (renameAlgEquiv e f) = f := by ext t; simp
  dsimp only [tateLift]
  rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, hcomm f]
  exact hf.trans (congrArg χ hren)

/-- Evaluating `tateLift hC χ` on `toTate σ K f` recovers `χ f`. -/
@[simp]
theorem tateLift_toTate (hC : IsAffinoidAlgebra K C) (χ : W σ →ₐ[K] C) (f : W σ) :
    tateLift hC χ (toTate σ K f) = χ f :=
  AlgHom.congr_fun (tateLift_comp_toTate hC χ) f

/-- `tateLift hC χ` is the unique `K`-algebra homomorphism `T_σ →ₐ[K] C` extending `χ`, with no
continuity hypothesis on the competing homomorphism. -/
theorem eq_tateLift (hC : IsAffinoidAlgebra K C) {χ : W σ →ₐ[K] C} {ψ : T σ →ₐ[K] C}
    (hψ : ψ.comp (toTate σ K) = χ) : ψ = tateLift hC χ := by
  have := (isAffinoidAlgebra_tate (K := K) (σ := σ)).isNoetherianRing
  apply AlgHom.coe_fn_injective
  exact denseRange_toTate.equalizer
    (IsAffinoidAlgebra.continuous_algHom (K := K) (A := C) (B := T σ) hC ψ)
    (continuous_tateLift hC χ)
    (funext fun f ↦ (AlgHom.congr_fun hψ f).trans (tateLift_toTate hC χ f).symm)

/-- **Universal property of `W_σ → T_σ` for affinoid targets.** Every `K`-algebra homomorphism
`W_σ →ₐ[K] C` into a completely normed affinoid algebra extends uniquely along `toTate σ K`. -/
theorem existsUnique_algHom_comp_toTate (hC : IsAffinoidAlgebra K C) (χ : W σ →ₐ[K] C) :
    ∃! ψ : T σ →ₐ[K] C, ψ.comp (toTate σ K) = χ :=
  ⟨tateLift hC χ, tateLift_comp_toTate hC χ, fun _ hψ ↦ eq_tateLift hC hψ⟩

/-- Lift a `K`-algebra homomorphism `χ : W_σ →ₐ[K] C` vanishing on `I` to `T_σ ⧸ I T_σ →ₐ[K] C`. -/
noncomputable def tateQuotientLift (hC : IsAffinoidAlgebra K C) (I : Ideal (W σ))
    (χ : W σ →ₐ[K] C) (hI : I ≤ RingHom.ker χ) :
    (T σ ⧸ I.map (toTate σ K)) →ₐ[K] C :=
  Ideal.Quotient.liftₐ (I.map (toTate σ K)) (tateLift hC χ) fun _ hx ↦ RingHom.mem_ker.mp <|
    (Ideal.map_le_iff_le_comap.mpr fun f hf ↦ Ideal.mem_comap.mpr <|
      RingHom.mem_ker.mpr ((tateLift_toTate hC χ f).trans (RingHom.mem_ker.mp (hI hf)))) hx

/-- `tateQuotientLift` evaluates on a quotient class `Ideal.Quotient.mk _ g` as
`tateLift hC χ g`. -/
@[simp]
theorem tateQuotientLift_mk (hC : IsAffinoidAlgebra K C) (I : Ideal (W σ))
    (χ : W σ →ₐ[K] C) (hI : I ≤ RingHom.ker χ) (g : T σ) :
    tateQuotientLift hC I χ hI (Ideal.Quotient.mk (I.map (toTate σ K)) g) = tateLift hC χ g :=
  (rfl)

/-- `tateQuotientLift` sends the class of `toTate σ K f` to `χ f`. -/
theorem tateQuotientLift_mk_toTate (hC : IsAffinoidAlgebra K C) (I : Ideal (W σ))
    (χ : W σ →ₐ[K] C) (hI : I ≤ RingHom.ker χ) (f : W σ) :
    tateQuotientLift hC I χ hI (Ideal.Quotient.mk (I.map (toTate σ K)) (toTate σ K f)) = χ f :=
  tateLift_toTate hC χ f

/-- `tateQuotientLift hC I χ hI` is continuous. -/
theorem continuous_tateQuotientLift (hC : IsAffinoidAlgebra K C) (I : Ideal (W σ))
    (χ : W σ →ₐ[K] C) (hI : I ≤ RingHom.ker χ) :
    Continuous (tateQuotientLift hC I χ hI) :=
  continuous_coinduced_dom.mpr <|
    (continuous_tateLift hC χ).congr fun g ↦ (tateQuotientLift_mk hC I χ hI g).symm

/-- `tateQuotientLift hC I χ hI` is the unique `K`-algebra homomorphism `T_σ ⧸ I T_σ →ₐ[K] C`
sending each class of `toTate σ K f` to `χ f`, with no continuity assumption on `ψ`. -/
theorem eq_tateQuotientLift (hC : IsAffinoidAlgebra K C) {I : Ideal (W σ)} {χ : W σ →ₐ[K] C}
    {hI : I ≤ RingHom.ker χ} {ψ : (T σ ⧸ I.map (toTate σ K)) →ₐ[K] C}
    (hψ : ∀ f : W σ, ψ (Ideal.Quotient.mk (I.map (toTate σ K)) (toTate σ K f)) = χ f) :
    ψ = tateQuotientLift hC I χ hI := by
  apply Ideal.Quotient.algHom_ext K
  have h1 : ψ.comp (Ideal.Quotient.mkₐ K _) = tateLift hC χ :=
    eq_tateLift hC (AlgHom.ext hψ)
  have h2 : (tateQuotientLift hC I χ hI).comp (Ideal.Quotient.mkₐ K _) = tateLift hC χ :=
    AlgHom.ext (tateQuotientLift_mk hC I χ hI)
  exact h1.trans h2.symm

/-- **Automatic continuity from `W_σ` into affinoid algebras.** Every `K`-algebra homomorphism
from `W_σ` into a completely normed `K`-affinoid algebra is continuous. -/
theorem continuous_algHom_of_isAffinoidAlgebra (hC : IsAffinoidAlgebra K C) (χ : W σ →ₐ[K] C) :
    Continuous χ := by
  rw [← tateLift_comp_toTate hC χ]
  exact (continuous_tateLift hC χ).comp isometry_toTate.continuous

end AffinoidTarget

/-- **Automatic continuity between Monsky–Washnitzer presentation quotients.** Every `K`-algebra
homomorphism `(W_σ ⧸ I) →ₐ[K] (W_τ ⧸ J)` is continuous for the quotient Gauss norms. -/
theorem continuous_algHom_quotient {I : Ideal (W σ)} {J : Ideal (W τ)}
    (φ : (W σ ⧸ I) →ₐ[K] (W τ ⧸ J)) : Continuous φ := by
  let J' : Ideal (T τ) := J.map (toTate τ K)
  let ιJ : W τ ⧸ J →ₐ[K] T τ ⧸ J' := Ideal.quotientMapₐ J' (toTate τ K) Ideal.le_comap_map
  have hιJ : Isometry ιJ := J.isometry_quotientMap_toTate
  have hcomp : Continuous (ιJ.comp (φ.comp (Ideal.Quotient.mkₐ K I))) :=
    continuous_algHom_of_isAffinoidAlgebra (K := K) (σ := σ) (C := T τ ⧸ J')
      ((isAffinoidAlgebra_tate (K := K) (σ := τ)).quotient J')
      (ιJ.comp (φ.comp (Ideal.Quotient.mkₐ K I)))
  exact continuous_coinduced_dom.mpr (hιJ.isEmbedding.isInducing.continuous_iff.mpr hcomp)

/-- Every `K`-algebra homomorphism between Monsky–Washnitzer presentation quotients is Lipschitz
for the quotient Gauss norms. -/
theorem exists_norm_map_le_quotient {I : Ideal (W σ)} {J : Ideal (W τ)}
    (φ : (W σ ⧸ I) →ₐ[K] (W τ ⧸ J)) : ∃ C > 0, ∀ x, ‖φ x‖ ≤ C * ‖x‖ := by
  let L : (W σ ⧸ I) →L[K] (W τ ⧸ J) := ⟨φ.toLinearMap, continuous_algHom_quotient φ⟩
  exact L.isBoundedLinearMap.bound

/-- Every `K`-algebra isomorphism between Monsky–Washnitzer presentation quotients is a
topological algebra isomorphism for the quotient Gauss norms. -/
noncomputable def quotientToContinuousAlgEquiv {I : Ideal (W σ)} {J : Ideal (W τ)}
    (e : (W σ ⧸ I) ≃ₐ[K] (W τ ⧸ J)) : (W σ ⧸ I) ≃A[K] (W τ ⧸ J) :=
  { e with
    continuous_toFun := continuous_algHom_quotient e.toAlgHom
    continuous_invFun := continuous_algHom_quotient e.symm.toAlgHom }

@[simp]
theorem quotientToContinuousAlgEquiv_apply {I : Ideal (W σ)} {J : Ideal (W τ)}
    (e : (W σ ⧸ I) ≃ₐ[K] (W τ ⧸ J)) (x : W σ ⧸ I) :
    quotientToContinuousAlgEquiv e x = e x := (rfl)

/-- The underlying algebra isomorphism of `quotientToContinuousAlgEquiv e` is `e`. -/
@[simp]
theorem toAlgEquiv_quotientToContinuousAlgEquiv {I : Ideal (W σ)} {J : Ideal (W τ)}
    (e : (W σ ⧸ I) ≃ₐ[K] (W τ ⧸ J)) :
    (quotientToContinuousAlgEquiv e).toAlgEquiv = e := (rfl)

/-- The inverse of `quotientToContinuousAlgEquiv e` is `quotientToContinuousAlgEquiv e.symm`. -/
@[simp]
theorem symm_quotientToContinuousAlgEquiv {I : Ideal (W σ)} {J : Ideal (W τ)}
    (e : (W σ ⧸ I) ≃ₐ[K] (W τ ⧸ J)) :
    (quotientToContinuousAlgEquiv e).symm = quotientToContinuousAlgEquiv e.symm := (rfl)

end washnitzerAlgebra

end WashnitzerAutomaticContinuity

/-! ### Universal property and functoriality of the affinoid completion -/

section CompletionUniversalProperty

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A C : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
  [NormedCommRing C] [NormedAlgebra K C] [IsUltrametricDist C] [CompleteSpace C]

/-- **Universal property of the affinoid completion.** Every `K`-algebra homomorphism
`χ : A →ₐ[K] C` from a dagger algebra into a completely normed `K`-affinoid algebra extends along
`toCompletion K A` to a `K`-algebra homomorphism `completion K A →ₐ[K] C`. -/
noncomputable def completionLift (hC : IsAffinoidAlgebra K C) (χ : A →ₐ[K] C) :
    completion K A →ₐ[K] C :=
  washnitzerAlgebra.tateQuotientLift (K := K) (σ := Fin (presentationDim K A)) (C := C)
    hC (RingHom.ker (presentation K A)) (χ.comp (presentation K A))
    fun f hf ↦ RingHom.mem_ker.mpr (by rw [AlgHom.comp_apply, RingHom.mem_ker.mp hf, map_zero])

variable {K}

/-- `completionLift K hC χ` extends `χ` on elements of `A`. -/
@[simp]
theorem completionLift_toCompletion (hC : IsAffinoidAlgebra K C) (χ : A →ₐ[K] C) (a : A) :
    completionLift K hC χ (toCompletion K A a) = χ a := by
  obtain ⟨f, rfl⟩ := presentation_surjective K A a
  rw [toCompletion_presentation, completionLift, washnitzerAlgebra.tateQuotientLift_mk_toTate,
    AlgHom.comp_apply]

/-- `completionLift K hC χ` extends `χ` along `toCompletion K A` as `K`-algebra homomorphisms. -/
@[simp]
theorem completionLift_comp_toCompletion (hC : IsAffinoidAlgebra K C) (χ : A →ₐ[K] C) :
    (completionLift K hC χ).comp (toCompletion K A) = χ :=
  AlgHom.ext (completionLift_toCompletion hC χ)

/-- `completionLift K hC χ` is continuous. -/
theorem continuous_completionLift (hC : IsAffinoidAlgebra K C) (χ : A →ₐ[K] C) :
    Continuous (completionLift K hC χ) :=
  washnitzerAlgebra.continuous_tateQuotientLift (K := K) (σ := Fin (presentationDim K A))
    hC _ _ _

/-- **Uniqueness of the extension to `completion K A`.** `completionLift K hC χ` is the unique
`K`-algebra homomorphism `completion K A →ₐ[K] C` extending `χ` along `toCompletion K A`, with no
continuity assumption on `ψ`. -/
theorem eq_completionLift (hC : IsAffinoidAlgebra K C) {χ : A →ₐ[K] C}
    {ψ : completion K A →ₐ[K] C} (hψ : ψ.comp (toCompletion K A) = χ) :
    ψ = completionLift K hC χ :=
  washnitzerAlgebra.eq_tateQuotientLift (K := K) (σ := Fin (presentationDim K A)) hC fun f ↦ by
    rw [← toCompletion_presentation, ← AlgHom.comp_apply, hψ, AlgHom.comp_apply]

variable (K) in
/-- Every `K`-algebra homomorphism `χ : A →ₐ[K] C` from a dagger algebra into a completely normed
`K`-affinoid algebra extends uniquely along `toCompletion K A`. -/
theorem existsUnique_algHom_comp_toCompletion (hC : IsAffinoidAlgebra K C) (χ : A →ₐ[K] C) :
    ∃! ψ : completion K A →ₐ[K] C, ψ.comp (toCompletion K A) = χ :=
  ⟨completionLift K hC χ, completionLift_comp_toCompletion hC χ, fun _ h ↦ eq_completionLift hC h⟩

end CompletionUniversalProperty

section CompletionFunctoriality

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
  [CommRing B] [Algebra K B] [IsDaggerAlgebra K B]
  [CommRing C] [Algebra K C] [IsDaggerAlgebra K C]

/-- **Functoriality of the affinoid completion** (Grosse-Klönne, Theorem 1.7 (1)). Every
`K`-algebra homomorphism `φ : A →ₐ[K] B` of dagger algebras induces a `K`-algebra homomorphism
`φ̂ : completion K A →ₐ[K] completion K B` compatible with `toCompletion`. -/
noncomputable def completionMap (φ : A →ₐ[K] B) : completion K A →ₐ[K] completion K B :=
  completionLift K (C := completion K B)
    (isAffinoidAlgebra_completion (K := K) (A := B)) ((toCompletion K B).comp φ)

variable {K}

/-- `completionMap K φ` commutes with `toCompletion` on elements of `A`. -/
@[simp]
theorem completionMap_toCompletion (φ : A →ₐ[K] B) (a : A) :
    completionMap K φ (toCompletion K A a) = toCompletion K B (φ a) := by
  have h := completionLift_toCompletion (K := K) (C := completion K B)
    (isAffinoidAlgebra_completion (K := K) (A := B)) ((toCompletion K B).comp φ) a
  have heq : completionMap K φ = completionLift K (C := completion K B)
      (isAffinoidAlgebra_completion (K := K) (A := B)) ((toCompletion K B).comp φ) := rfl
  exact (AlgHom.congr_fun heq (toCompletion K A a)).trans h

/-- `completionMap K φ` commutes with `toCompletion` as `K`-algebra homomorphisms. -/
@[simp]
theorem completionMap_comp_toCompletion (φ : A →ₐ[K] B) :
    (completionMap K φ).comp (toCompletion K A) = (toCompletion K B).comp φ :=
  AlgHom.ext (completionMap_toCompletion φ)

/-- `completionMap K φ` is continuous. -/
theorem continuous_completionMap (φ : A →ₐ[K] B) : Continuous (completionMap K φ) := by
  have h := continuous_completionLift (K := K) (C := completion K B)
    (isAffinoidAlgebra_completion (K := K) (A := B)) ((toCompletion K B).comp φ)
  have heq : completionMap K φ = completionLift K (C := completion K B)
      (isAffinoidAlgebra_completion (K := K) (A := B)) ((toCompletion K B).comp φ) := rfl
  exact heq ▸ h

/-- **Uniqueness of the completed morphism.** `completionMap K φ` is the unique `K`-algebra
homomorphism `completion K A →ₐ[K] completion K B` commuting with `toCompletion`, with no
continuity assumption on `ψ`. -/
theorem eq_completionMap {φ : A →ₐ[K] B} {ψ : completion K A →ₐ[K] completion K B}
    (hψ : ψ.comp (toCompletion K A) = (toCompletion K B).comp φ) :
    ψ = completionMap K φ := by
  unfold completionMap
  exact eq_completionLift (K := K) (C := completion K B)
    (isAffinoidAlgebra_completion (K := K) (A := B)) hψ

variable (K) in
/-- Every `K`-algebra homomorphism `φ : A →ₐ[K] B` extends uniquely along `toCompletion` to a
`K`-algebra homomorphism between the affinoid completions. -/
theorem existsUnique_completion_algHom (φ : A →ₐ[K] B) :
    ∃! ψ : completion K A →ₐ[K] completion K B,
      ψ.comp (toCompletion K A) = (toCompletion K B).comp φ :=
  ⟨completionMap K φ, completionMap_comp_toCompletion φ, fun _ h ↦ eq_completionMap h⟩

/-- Completing the identity homomorphism gives the identity on `completion K A`. -/
@[simp]
theorem completionMap_id :
    completionMap K (AlgHom.id K A) = AlgHom.id K (completion K A) :=
  (eq_completionMap rfl).symm

/-- `completionMap` preserves composition of `K`-algebra homomorphisms. -/
@[simp]
theorem completionMap_comp (ψ : B →ₐ[K] C) (φ : A →ₐ[K] B) :
    completionMap K (ψ.comp φ) = (completionMap K ψ).comp (completionMap K φ) :=
  (eq_completionMap <| by
    rw [AlgHom.comp_assoc, completionMap_comp_toCompletion, ← AlgHom.comp_assoc,
      completionMap_comp_toCompletion, AlgHom.comp_assoc]).symm

variable (K) in
/-- Functoriality of `completion` on `K`-algebra isomorphisms, bundled as a topological algebra
isomorphism. -/
noncomputable def completionContinuousAlgEquiv (e : A ≃ₐ[K] B) :
    completion K A ≃A[K] completion K B :=
  IsAffinoidAlgebra.toContinuousAlgEquiv (K := K) (A := completion K A) (B := completion K B)
    (isAffinoidAlgebra_completion (K := K) (A := B)) <|
    AlgEquiv.ofAlgHom (completionMap K e.toAlgHom) (completionMap K e.symm.toAlgHom)
      (by simp [← completionMap_comp])
      (by simp [← completionMap_comp])

@[simp]
theorem completionContinuousAlgEquiv_apply (e : A ≃ₐ[K] B) (x : completion K A) :
    completionContinuousAlgEquiv K e x = completionMap K e.toAlgHom x := by
  simp [completionContinuousAlgEquiv]

@[simp]
theorem completionContinuousAlgEquiv_symm (e : A ≃ₐ[K] B) :
    (completionContinuousAlgEquiv K e).symm = completionContinuousAlgEquiv K e.symm := by
  ext x
  simp [completionContinuousAlgEquiv]

@[simp]
theorem completionContinuousAlgEquiv_refl :
    completionContinuousAlgEquiv K (AlgEquiv.refl : A ≃ₐ[K] A) = ContinuousAlgEquiv.refl K _ := by
  ext x
  simp

/-- `completionContinuousAlgEquiv` preserves composition of `K`-algebra isomorphisms. -/
@[simp]
theorem completionContinuousAlgEquiv_trans (e₁ : A ≃ₐ[K] B) (e₂ : B ≃ₐ[K] C) :
    completionContinuousAlgEquiv K (e₁.trans e₂) =
      (completionContinuousAlgEquiv K e₁).trans (completionContinuousAlgEquiv K e₂) := by
  ext x
  simp only [completionContinuousAlgEquiv_apply, ContinuousAlgEquiv.trans_apply]
  have h : (e₁.trans e₂).toAlgHom = e₂.toAlgHom.comp e₁.toAlgHom := rfl
  simp [h]

end CompletionFunctoriality

/-! ### Independence of presentation for the affinoid completion -/

section PresentationCompletion

variable {K σ : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Finite σ] {A : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]

local notation "W " α:max => washnitzerAlgebra α K
local notation "T " α:max => IsRestricted.subring (R := K) (fun _ : α ↦ (1 : ℝ))

private noncomputable def presentationToCompletion (π : W σ →ₐ[K] A) :
    (T σ ⧸ (RingHom.ker π).map (washnitzerAlgebra.toTate σ K)) →ₐ[K] completion K A :=
  washnitzerAlgebra.tateQuotientLift (K := K) (σ := σ) (C := completion K A)
    (isAffinoidAlgebra_completion (K := K) (A := A)) (RingHom.ker π) ((toCompletion K A).comp π)
    fun f hf ↦ RingHom.mem_ker.mpr (by rw [AlgHom.comp_apply, RingHom.mem_ker.mp hf, map_zero])

private noncomputable def completionToPresentation (π : W σ →ₐ[K] A)
    (hπ : Function.Surjective π) :
    completion K A →ₐ[K] (T σ ⧸ (RingHom.ker π).map (washnitzerAlgebra.toTate σ K)) :=
  let J : Ideal (T σ) := (RingHom.ker π).map (washnitzerAlgebra.toTate σ K)
  let τπ : A →ₐ[K] T σ ⧸ J :=
    (Ideal.quotientMapₐ J (washnitzerAlgebra.toTate σ K) Ideal.le_comap_map).comp
      (Ideal.quotientKerAlgEquivOfSurjective hπ).symm.toAlgHom
  completionLift K (C := T σ ⧸ J) ((isAffinoidAlgebra_tate (K := K) (σ := σ)).quotient J) τπ

/-- **Presentation-independence of the affinoid completion.** For any surjective `K`-algebra
presentation `π : W_σ →ₐ[K] A`, the quotient `T_σ ⧸ (ker π) T_σ` is canonically isomorphic as a
topological `K`-algebra to `completion K A`, compatibly with `π` and `toCompletion`. -/
noncomputable def presentationCompletionEquiv (π : W σ →ₐ[K] A) (hπ : Function.Surjective π) :
    (T σ ⧸ (RingHom.ker π).map (washnitzerAlgebra.toTate σ K)) ≃A[K] completion K A := by
  let J : Ideal (T σ) := (RingHom.ker π).map (washnitzerAlgebra.toTate σ K)
  have hQ : IsAffinoidAlgebra K (T σ ⧸ J) := (isAffinoidAlgebra_tate (K := K) (σ := σ)).quotient J
  let fwd := presentationToCompletion π
  let bwd := completionToPresentation π hπ
  have hfwd (f : W σ) :
      fwd (Ideal.Quotient.mk J (washnitzerAlgebra.toTate σ K f)) = toCompletion K A (π f) :=
    washnitzerAlgebra.tateQuotientLift_mk_toTate _ _ _ _ f
  have hbwd (f : W σ) :
      bwd (toCompletion K A (π f)) = Ideal.Quotient.mk J (washnitzerAlgebra.toTate σ K f) := by
    let τπ : A →ₐ[K] T σ ⧸ J :=
      (Ideal.quotientMapₐ J (washnitzerAlgebra.toTate σ K) Ideal.le_comap_map).comp
        (Ideal.quotientKerAlgEquivOfSurjective hπ).symm.toAlgHom
    have h := completionLift_toCompletion (K := K) (C := T σ ⧸ J) hQ τπ (π f)
    have heq : bwd = completionLift K (C := T σ ⧸ J) hQ τπ := rfl
    exact ((AlgHom.congr_fun heq (toCompletion K A (π f))).trans h).trans (by simp [τπ, J])
  have hfb : fwd.comp bwd = AlgHom.id K (completion K A) := by
    rw [← completionMap_id (K := K) (A := A)]
    exact eq_completionMap (by
      ext a
      obtain ⟨f, rfl⟩ := hπ a
      simp [hbwd, hfwd])
  have hbf : bwd.comp fwd = AlgHom.id K (T σ ⧸ J) := by
    have uniq (ψ : (T σ ⧸ J) →ₐ[K] (T σ ⧸ J))
        (hψ : ∀ f : W σ,
          ψ (Ideal.Quotient.mk J (washnitzerAlgebra.toTate σ K f)) =
            Ideal.Quotient.mk J (washnitzerAlgebra.toTate σ K f)) :=
      washnitzerAlgebra.eq_tateQuotientLift (K := K) (σ := σ) (C := T σ ⧸ J) hQ
        (I := RingHom.ker π)
        (χ := (Ideal.Quotient.mkₐ K J).comp (washnitzerAlgebra.toTate σ K))
        (hI := fun f hf ↦ RingHom.mem_ker.mpr (by
          rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.mem_map_of_mem _ hf))
        (ψ := ψ) hψ
    exact (uniq (bwd.comp fwd) fun f ↦ by simp [hfwd, hbwd]).trans
      (uniq (AlgHom.id K (T σ ⧸ J)) fun f ↦ by simp).symm
  exact IsAffinoidAlgebra.toContinuousAlgEquiv (K := K) (A := T σ ⧸ J) (B := completion K A)
    (isAffinoidAlgebra_completion (K := K) (A := A)) (AlgEquiv.ofAlgHom fwd bwd hfb hbf)

/-- `presentationCompletionEquiv π hπ` sends the class of `toTate σ K f` to
`toCompletion K A (π f)`. -/
@[simp]
theorem presentationCompletionEquiv_mk_toTate (π : W σ →ₐ[K] A) (hπ : Function.Surjective π)
    (f : W σ) :
    presentationCompletionEquiv π hπ (Ideal.Quotient.mk _ (washnitzerAlgebra.toTate σ K f)) =
      toCompletion K A (π f) := by
  simp [presentationCompletionEquiv, presentationToCompletion]

/-- The inverse of `presentationCompletionEquiv π hπ` sends `toCompletion K A (π f)` to the class of
`toTate σ K f`. -/
@[simp]
theorem presentationCompletionEquiv_symm_toCompletion (π : W σ →ₐ[K] A)
    (hπ : Function.Surjective π) (f : W σ) :
    (presentationCompletionEquiv π hπ).symm (toCompletion K A (π f)) =
      Ideal.Quotient.mk _ (washnitzerAlgebra.toTate σ K f) :=
  (presentationCompletionEquiv π hπ).symm_apply_eq.mpr
    (presentationCompletionEquiv_mk_toTate π hπ f).symm

variable (K σ) in
/-- **The affinoid completion of the Monsky–Washnitzer algebra `W_σ` is the Tate algebra `T_σ`**,
compatibly with `toCompletion` and `toTate`. -/
noncomputable def completionWashnitzerEquiv : completion K (W σ) ≃A[K] T σ :=
  (presentationCompletionEquiv (AlgHom.id K (W σ)) Function.surjective_id).symm.trans <|
    IsAffinoidAlgebra.toContinuousAlgEquiv (K := K)
      (A := T σ ⧸ (RingHom.ker (AlgHom.id K (W σ))).map (washnitzerAlgebra.toTate σ K))
      (B := T σ) (isAffinoidAlgebra_tate (K := K) (σ := σ)) <|
      (Ideal.quotientEquivAlgOfEq K <| by
        rw [(RingHom.injective_iff_ker_eq_bot _).mp Function.injective_id, Ideal.map_bot]).trans
        (AlgEquiv.quotientBot K (T σ))

@[simp]
theorem completionWashnitzerEquiv_toCompletion (f : W σ) :
    completionWashnitzerEquiv K σ (toCompletion K (W σ) f) = washnitzerAlgebra.toTate σ K f := by
  have h := presentationCompletionEquiv_symm_toCompletion
    (AlgHom.id K (W σ)) Function.surjective_id f
  simp only [AlgHom.id_apply] at h
  simp [completionWashnitzerEquiv, h]

@[simp]
theorem completionWashnitzerEquiv_symm_toTate (f : W σ) :
    (completionWashnitzerEquiv K σ).symm (washnitzerAlgebra.toTate σ K f) =
      toCompletion K (W σ) f :=
  (completionWashnitzerEquiv K σ).symm_apply_eq.mpr
    (completionWashnitzerEquiv_toCompletion f).symm

/-- **The affinoid completion of a presentation quotient `W_σ ⧸ I` is `T_σ ⧸ I T_σ`**, compatibly
with `toCompletion` and `toTate`. -/
noncomputable def completionQuotientEquiv (I : Ideal (W σ)) :
    completion K (W σ ⧸ I) ≃A[K] (T σ ⧸ I.map (washnitzerAlgebra.toTate σ K)) :=
  (presentationCompletionEquiv (Ideal.Quotient.mkₐ K I)
    (Ideal.Quotient.mkₐ_surjective K I)).symm.trans <|
    IsAffinoidAlgebra.toContinuousAlgEquiv (K := K)
      (A := T σ ⧸ (RingHom.ker (Ideal.Quotient.mkₐ K I)).map (washnitzerAlgebra.toTate σ K))
      (B := T σ ⧸ I.map (washnitzerAlgebra.toTate σ K))
      ((isAffinoidAlgebra_tate (K := K) (σ := σ)).quotient _)
      (Ideal.quotientEquivAlgOfEq K
        (congrArg (Ideal.map (washnitzerAlgebra.toTate σ K)) (Ideal.Quotient.mkₐ_ker K I)))

@[simp]
theorem completionQuotientEquiv_toCompletion_mk (I : Ideal (W σ)) (f : W σ) :
    completionQuotientEquiv I (toCompletion K (W σ ⧸ I) (Ideal.Quotient.mk I f)) =
      Ideal.Quotient.mk (I.map (washnitzerAlgebra.toTate σ K))
        (washnitzerAlgebra.toTate σ K f) := by
  have h := presentationCompletionEquiv_symm_toCompletion (Ideal.Quotient.mkₐ K I)
    (Ideal.Quotient.mkₐ_surjective K I) f
  simp only [Ideal.Quotient.mkₐ_eq_mk] at h
  simp [completionQuotientEquiv, h]

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

end PresentationCompletion

/-! ### Automatic continuity and equivalence of presentation norms on dagger algebras -/

section DaggerContinuity

variable {K σ τ : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Finite σ] [Finite τ]

local notation "W " α:max => washnitzerAlgebra α K

/-- **Equivalence of Monsky–Washnitzer presentations.** Any two surjective presentations of a
`K`-algebra `D` by Monsky–Washnitzer algebras yield canonically homeomorphic residue algebras for
their quotient Gauss norms. -/
noncomputable def presentationContinuousAlgEquiv {D : Type*} [CommRing D] [Algebra K D]
    (π₁ : W σ →ₐ[K] D) (hπ₁ : Function.Surjective π₁)
    (π₂ : W τ →ₐ[K] D) (hπ₂ : Function.Surjective π₂) :
    (W σ ⧸ RingHom.ker π₁) ≃A[K] (W τ ⧸ RingHom.ker π₂) :=
  washnitzerAlgebra.quotientToContinuousAlgEquiv
    ((Ideal.quotientKerAlgEquivOfSurjective hπ₁).trans
      (Ideal.quotientKerAlgEquivOfSurjective hπ₂).symm)

/-- The underlying algebra isomorphism of `presentationContinuousAlgEquiv`. -/
@[simp]
theorem toAlgEquiv_presentationContinuousAlgEquiv {D : Type*} [CommRing D] [Algebra K D]
    (π₁ : W σ →ₐ[K] D) (hπ₁ : Function.Surjective π₁)
    (π₂ : W τ →ₐ[K] D) (hπ₂ : Function.Surjective π₂) :
    (presentationContinuousAlgEquiv π₁ hπ₁ π₂ hπ₂).toAlgEquiv =
      (Ideal.quotientKerAlgEquivOfSurjective hπ₁).trans
        (Ideal.quotientKerAlgEquivOfSurjective hπ₂).symm :=
  (rfl)

/-- The inverse of `presentationContinuousAlgEquiv` swaps the two presentations. -/
@[simp]
theorem symm_presentationContinuousAlgEquiv {D : Type*} [CommRing D] [Algebra K D]
    (π₁ : W σ →ₐ[K] D) (hπ₁ : Function.Surjective π₁)
    (π₂ : W τ →ₐ[K] D) (hπ₂ : Function.Surjective π₂) :
    (presentationContinuousAlgEquiv π₁ hπ₁ π₂ hπ₂).symm =
      presentationContinuousAlgEquiv π₂ hπ₂ π₁ hπ₁ := by
  ext x
  simp [presentationContinuousAlgEquiv]

/-- `presentationContinuousAlgEquiv` sends the residue class of `d` in the first presentation to
its residue class in the second presentation. -/
@[simp]
theorem presentationContinuousAlgEquiv_quotientKerAlgEquivOfSurjective_symm
    {D : Type*} [CommRing D] [Algebra K D]
    (π₁ : W σ →ₐ[K] D) (hπ₁ : Function.Surjective π₁)
    (π₂ : W τ →ₐ[K] D) (hπ₂ : Function.Surjective π₂) (d : D) :
    presentationContinuousAlgEquiv π₁ hπ₁ π₂ hπ₂
        ((Ideal.quotientKerAlgEquivOfSurjective hπ₁).symm d) =
      (Ideal.quotientKerAlgEquivOfSurjective hπ₂).symm d := by
  simp [presentationContinuousAlgEquiv]

/-- `presentationContinuousAlgEquiv` commutes with the maps to `D` induced by both presentations. -/
@[simp]
theorem kerLiftAlg_presentationContinuousAlgEquiv {D : Type*} [CommRing D] [Algebra K D]
    (π₁ : W σ →ₐ[K] D) (hπ₁ : Function.Surjective π₁)
    (π₂ : W τ →ₐ[K] D) (hπ₂ : Function.Surjective π₂) (x : W σ ⧸ RingHom.ker π₁) :
    Ideal.kerLiftAlg π₂ (presentationContinuousAlgEquiv π₁ hπ₁ π₂ hπ₂ x) =
      Ideal.kerLiftAlg π₁ x := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨g, hg⟩ := hπ₂ (π₁ f)
  simp [presentationContinuousAlgEquiv, ← hg]

/-- On `W_σ` with its Gauss norm, `toCompletion` is a topological embedding. -/
theorem isEmbedding_toCompletion_washnitzerAlgebra :
    Topology.IsEmbedding (toCompletion K (W σ)) := by
  have h : ⇑(completionWashnitzerEquiv K σ) ∘ ⇑(toCompletion K (W σ)) =
      ⇑(washnitzerAlgebra.toTate σ K) := funext completionWashnitzerEquiv_toCompletion
  exact (completionWashnitzerEquiv K σ).toHomeomorph.isEmbedding.of_comp_iff.mp
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

namespace IsDaggerAlgebra

variable {A B : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
  [CommRing B] [Algebra K B] [IsDaggerAlgebra K B]

/-- **Automatic continuity from a dagger algebra into an affinoid algebra.** If `A` carries the
topology induced from `toCompletion K A`, then every `K`-algebra homomorphism `χ : A →ₐ[K] C` into
a completely normed `K`-affinoid algebra is continuous. -/
theorem continuous_algHom_of_isAffinoidAlgebra [TopologicalSpace A]
    (hA : Topology.IsInducing (toCompletion K A))
    {C : Type*} [NormedCommRing C] [NormedAlgebra K C] [IsUltrametricDist C] [CompleteSpace C]
    (hC : IsAffinoidAlgebra K C) (χ : A →ₐ[K] C) : Continuous χ := by
  rw [← completionLift_comp_toCompletion hC χ]
  exact (continuous_completionLift hC χ).comp hA.continuous

/-- **Automatic continuity of homomorphisms of dagger algebras** (general topology form). If `A`
and `B` carry the topologies induced from their affinoid completions along `toCompletion` — for
instance `W_σ`, `W_σ ⧸ I`, or `residueNormedCommRing` — then every `K`-algebra homomorphism
`φ : A →ₐ[K] B` is continuous. -/
theorem continuous_algHom_of_isInducing [TopologicalSpace A] [TopologicalSpace B]
    (hA : Topology.IsInducing (toCompletion K A)) (hB : Topology.IsInducing (toCompletion K B))
    (φ : A →ₐ[K] B) : Continuous φ :=
  hB.continuous_iff.mpr <|
    continuous_algHom_of_isAffinoidAlgebra (C := completion K B) hA
      (isAffinoidAlgebra_completion (K := K) (A := B)) ((toCompletion K B).comp φ)

/-- **Automatic continuity of homomorphisms of dagger algebras** (Grosse-Klönne, Proposition
1.6 (2)). Every `K`-algebra homomorphism `φ : A →ₐ[K] B` is continuous for the residue norms of `A`
and `B`. -/
theorem continuous_algHom (φ : A →ₐ[K] B) :
    letI := residueNormedCommRing K A
    letI := residueNormedCommRing K B
    Continuous φ :=
  letI := residueNormedCommRing K A
  letI := residueNormedCommRing K B
  continuous_algHom_of_isInducing
    (isometry_toCompletion K A).isEmbedding.isInducing
    (isometry_toCompletion K B).isEmbedding.isInducing φ

/-- **Automatic uniform continuity of homomorphisms of dagger algebras** (general uniformity form).
If `A` and `B` carry uniform additive group structures whose topologies are induced from their
affinoid completions along `toCompletion`, then every `K`-algebra homomorphism `φ : A →ₐ[K] B` is
uniformly continuous. -/
theorem uniformContinuous_algHom_of_isInducing [UniformSpace A] [IsUniformAddGroup A]
    [UniformSpace B] [IsUniformAddGroup B]
    (hA : Topology.IsInducing (toCompletion K A)) (hB : Topology.IsInducing (toCompletion K B))
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
    (isometry_toCompletion K A).isEmbedding.isInducing
    (isometry_toCompletion K B).isEmbedding.isInducing φ

/-- **Lipschitz bound for homomorphisms of dagger algebras.** Every `K`-algebra homomorphism
`φ : A →ₐ[K] B` is bounded with respect to the residue norms. -/
theorem exists_norm_map_le (φ : A →ₐ[K] B) :
    letI := residueNormedCommRing K A
    letI := residueNormedCommRing K B
    ∃ C > 0, ∀ a, ‖φ a‖ ≤ C * ‖a‖ :=
  letI := residueNormedCommRing K A
  letI := residueNormedAlgebra K A
  letI := residueNormedCommRing K B
  letI := residueNormedAlgebra K B
  let L : A →L[K] B := ⟨φ.toLinearMap, continuous_algHom φ⟩
  L.isBoundedLinearMap.bound

/-- An element of a dagger algebra carrying the topology induced from its affinoid completion is
power-bounded if and only if its image in `completion K A` is power-bounded. -/
theorem isPowerBounded_toCompletion_iff [TopologicalSpace A]
    (hA : Topology.IsInducing (toCompletion K A)) {a : A} :
    Huber.IsPowerBounded (toCompletion K A a) ↔ Huber.IsPowerBounded a := by
  have hτA : ‹TopologicalSpace A› =
      (residueNormedCommRing K A).toUniformSpace.toTopologicalSpace :=
    hA.eq_induced.trans (residueNormedCommRing_toTopologicalSpace_eq_induced K A).symm
  subst hτA
  let := residueNormedCommRing K A
  let := residueNormedAlgebra K A
  obtain ⟨ϖ, hϖ0, hϖ1⟩ := NormedField.exists_norm_lt_one K
  have hϖK : Huber.IsPseudoUniformizer ϖ :=
    Huber.IsPseudoUniformizer.of_norm_lt_one (isUnit_iff_ne_zero.mpr (norm_pos_iff.mp hϖ0)) hϖ1
  have hϖA := hϖK.map (continuous_algebraMap K A)
  have hϖÂ := hϖA.map (φ := toCompletion K A) (isometry_toCompletion K A).continuous
  rw [Huber.isPowerBounded_iff, Huber.isPowerBounded_iff,
    Huber.IsPseudoUniformizer.isBounded_iff_forall_norm_le (R := completion K A) hϖÂ,
    Huber.IsPseudoUniformizer.isBounded_iff_forall_norm_le (R := A) hϖA]
  simp only [Set.forall_mem_range, ← map_pow, norm_toCompletion K A]

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
    hC (completionLift K hC χ) ((isPowerBounded_toCompletion_iff hA).mpr ha)

/-- Every `K`-algebra homomorphism of dagger algebras maps power-bounded elements to power-bounded
elements (for the canonical topologies induced from `toCompletion`). -/
theorem isPowerBounded_map [TopologicalSpace A] [TopologicalSpace B]
    (hA : Topology.IsInducing (toCompletion K A)) (hB : Topology.IsInducing (toCompletion K B))
    (φ : A →ₐ[K] B) {a : A} (ha : Huber.IsPowerBounded a) :
    Huber.IsPowerBounded (φ a) :=
  (isPowerBounded_toCompletion_iff hB).mp <|
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
    let e := presentationContinuousAlgEquiv (presentation K A) (presentation_surjective K A) π hπ
    obtain ⟨c₂, hc₂, hub⟩ := washnitzerAlgebra.exists_norm_map_le_quotient e.toAlgHom
    obtain ⟨d, hd, hlb⟩ := washnitzerAlgebra.exists_norm_map_le_quotient e.symm.toAlgHom
    refine ⟨d⁻¹, inv_pos.mpr hd, c₂, hc₂, fun a ↦ ?_⟩
    have he : e (residueAlgEquiv K A a) = (Ideal.quotientKerAlgEquivOfSurjective hπ).symm a := by
      rw [residueAlgEquiv_def]
      exact presentationContinuousAlgEquiv_quotientKerAlgEquivOfSurjective_symm _
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
  let φ := presentationContinuousAlgEquiv π hπ (presentation K A) (presentation_surjective K A)
  have hφ : ⇑φ ∘ ⇑e₁ = ⇑e₂ := funext fun a ↦
    (presentationContinuousAlgEquiv_quotientKerAlgEquivOfSurjective_symm π hπ _
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
  washnitzerAlgebra.continuous_algHom_quotient _

-- Automatic continuity holds on nonreduced dagger algebras such as `W_1 ⧸ (X²)`.
example (φ : (W (Fin 1) ⧸ Ideal.span {washnitzerAlgebra.X (Fin 1) K 0 ^ 2}) →ₐ[K]
    (W (Fin 1) ⧸ Ideal.span {washnitzerAlgebra.X (Fin 1) K 0 ^ 2})) :
    Continuous φ :=
  washnitzerAlgebra.continuous_algHom_quotient φ

end Examples

end DaggerContinuity

end TauCeti.Dagger
