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
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UniversalProperty

import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import TauCeti.Analysis.Normed.Algebra.Completion
import TauCeti.RingTheory.Affinoid.Continuity
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
   `T_σ` (`TauCeti.MvPowerSeries.restrictedLift`) produces a continuous map `ψ : T_σ → C` agreeing
   with `χ` on polynomials.
3. Modulo every `𝔪^k` (`𝔪` maximal in `C`), `C ⧸ 𝔪^k` is finite-dimensional and Hausdorff, so `χ`
   and `ψ ∘ toTate` are continuous and agree on dense polynomials; Krull's intersection theorem in
   `C` gives `ψ ∘ toTate = χ`.

Applied to `A → B → B̂`, this makes completion functorial (`TauCeti.Dagger.completionMap`),
identifies `T_σ ⧸ (ker π) T_σ` with `completion K A` for any presentation `π : W_σ ↠ A`
(`TauCeti.Dagger.presentationCompletionEquiv`), and reduces continuity and Lipschitz bounds for
arbitrary `K`-algebra homomorphisms `A →ₐ[K] B` of dagger algebras to automatic continuity for
their affinoid completions (`TauCeti.IsAffinoidAlgebra.continuous_algHom`). In particular, all
Monsky–Washnitzer presentations of `A` induce equivalent residue norms and the same uniformity.

## Main definitions

* `TauCeti.Dagger.washnitzerAlgebra.tateLift` and `tateQuotientLift`: the unique extension of
  `W_σ →ₐ[K] C` to `T_σ →ₐ[K] C` (and to `T_σ ⧸ I T_σ →ₐ[K] C`) for an affinoid target `C`.
* `TauCeti.Dagger.completionMap` and `TauCeti.Dagger.completionContinuousAlgEquiv`: functoriality
  `φ ↦ φ̂` of affinoid completions on `K`-algebra homomorphisms and isomorphisms.
* `TauCeti.Dagger.presentationCompletionEquiv`, `TauCeti.Dagger.completionWashnitzerEquiv`, and
  `TauCeti.Dagger.completionQuotientEquiv`: presentation-independence `T_σ ⧸ (ker π) T_σ ≃A[K] Â`.
* `TauCeti.Dagger.residueCompletionAlgEquiv`: metric completion comparison
  `UniformSpace.Completion A ≃ₐ[K] completion K A`.
* `TauCeti.Dagger.presentationContinuousAlgEquiv`: topological algebra isomorphism between residue
  algebras of any two Monsky–Washnitzer presentations.

## Main results

* `TauCeti.Dagger.washnitzerAlgebra.continuous_algHom_of_isAffinoidAlgebra`: automatic continuity
  from `W_σ` into completely normed affinoid algebras.
* `TauCeti.Dagger.eq_completionMap`: uniqueness of `completionMap K φ` with no continuity
  assumption.
* `TauCeti.Dagger.IsDaggerAlgebra.continuous_algHom_of_isInducing`,
  `TauCeti.Dagger.IsDaggerAlgebra.continuous_algHom`, and
  `TauCeti.Dagger.IsDaggerAlgebra.exists_norm_map_le`: automatic continuity and Lipschitz bounds
  for `K`-algebra homomorphisms of dagger algebras.
* `TauCeti.Dagger.exists_norm_presentation_equiv` and
  `TauCeti.Dagger.induced_uniformSpace_presentation_eq`: equivalence of presentation residue norms
  and equality of induced uniformities.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1, Proposition 1.6 and Theorem 1.7 (1).
* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert],
  §§3.7.5 and 6.1.3.
-/

public section

open Filter Topology UniformSpace _root_.MvPowerSeries

namespace TauCeti.Dagger

/-- Upgrade a `K`-algebra equivalence between completely normed affinoid algebras to a topological
algebra equivalence, avoiding noncommutative quotient norm diamond imports on ideal quotients. -/
private noncomputable def affinoidToContinuousAlgEquiv {K A B : Type*}
    [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A]
    [NormedCommRing B] [NormedAlgebra K B] [IsUltrametricDist B] [CompleteSpace B]
    (hB : IsAffinoidAlgebra K B) (e : A ≃ₐ[K] B) : A ≃A[K] B :=
  have hA : IsAffinoidAlgebra K A := hB.of_surjective e.symm.toAlgHom e.symm.surjective
  have := hA.isNoetherianRing
  have := hB.isNoetherianRing
  { e with
    continuous_toFun := IsAffinoidAlgebra.continuous_algHom (K := K) (A := B) (B := A) hB e.toAlgHom
    continuous_invFun :=
      IsAffinoidAlgebra.continuous_algHom (K := K) (A := A) (B := B) hA e.symm.toAlgHom }

@[simp]
private theorem affinoidToContinuousAlgEquiv_apply {K A B : Type*}
    [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A]
    [NormedCommRing B] [NormedAlgebra K B] [IsUltrametricDist B] [CompleteSpace B]
    (hB : IsAffinoidAlgebra K B) (e : A ≃ₐ[K] B) (a : A) :
    affinoidToContinuousAlgEquiv hB e a = e a := (rfl)

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

private noncomputable def tateLiftFin {n : ℕ} (hC : IsAffinoidAlgebra K C)
    (χ : W (Fin n) →ₐ[K] C) : T (Fin n) →ₐ[K] C where
  __ := TauCeti.MvPowerSeries.restrictedLift (continuous_algebraMap K C)
    fun i ↦ isPowerBounded_map_of_norm_le_one hC χ (norm_X i).le
  commutes' r := TauCeti.MvPowerSeries.restrictedLift_algebraMap _ _ r

private theorem continuous_tateLiftFin {n : ℕ} (hC : IsAffinoidAlgebra K C)
    (χ : W (Fin n) →ₐ[K] C) : Continuous (tateLiftFin hC χ) :=
  TauCeti.MvPowerSeries.continuous_restrictedLift _ _

private theorem tateLiftFin_comp_toTate {n : ℕ} (hC : IsAffinoidAlgebra K C)
    (χ : W (Fin n) →ₐ[K] C) : (tateLiftFin hC χ).comp (toTate (Fin n) K) = χ := by
  have := hC.isNoetherianRing
  have hpoly : ((tateLiftFin hC χ).comp (toTate (Fin n) K)).comp (ofMvPolynomial (Fin n) K) =
      χ.comp (ofMvPolynomial (Fin n) K) := by
    apply MvPolynomial.algHom_ext
    intro i
    have hX : toTate (Fin n) K (X (Fin n) K i) =
        ⟨_root_.MvPowerSeries.X i, isRestricted_X _ i⟩ := Subtype.ext (by simp)
    simp [tateLiftFin, hX]
  ext f
  suffices tateLiftFin hC χ (toTate (Fin n) K f) - χ f ∈ (⊥ : Ideal C) from sub_eq_zero.mp this
  rw [← Ideal.iInf_isMaximal_pow_eq_bot]
  simp only [Ideal.mem_iInf]
  intro m hm k _
  let := hm
  let I := m ^ k
  have : IsClosed (I : Set C) := hC.isClosed_ideal I
  have : Module.Finite K (C ⧸ I) := hC.finite_quotient_pow m k
  let q : C →ₐ[K] C ⧸ I := Ideal.Quotient.mkₐ K I
  -- Modulo `m ^ k`, both maps from `W_{Fin n}` are continuous and agree on dense polynomials.
  have hcont₁ : Continuous (q.comp ((tateLiftFin hC χ).comp (toTate (Fin n) K))) :=
    continuous_quot_mk.comp ((continuous_tateLiftFin hC χ).comp isometry_toTate.continuous)
  have hcont₂ : Continuous (q.comp χ) := continuous_algHom_of_finiteDimensional (q.comp χ)
  have heq : ⇑(q.comp ((tateLiftFin hC χ).comp (toTate (Fin n) K))) = ⇑(q.comp χ) :=
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
  (tateLiftFin hC (χ.comp (renameAlgEquiv e.symm).toAlgHom)).comp
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
  have hf := AlgHom.congr_fun (tateLiftFin_comp_toTate hC
    (χ.comp (renameAlgEquiv e.symm).toAlgHom)) (renameAlgEquiv e f)
  have hren : renameAlgEquiv e.symm (renameAlgEquiv e f) = f := by ext t; simp
  -- Unfold `tateLift` to `tateLiftFin` composed with variable renaming before rewriting `hcomm`.
  change tateLiftFin hC (χ.comp (renameAlgEquiv e.symm).toAlgHom)
    (IsRestricted.renameAlgEquiv e (fun _ ↦ (1 : ℝ)) (toTate σ K f)) = χ f
  rw [hcomm f]
  exact hf.trans (congrArg χ hren)

/-- Evaluating `tateLift hC χ` on `toTate σ K f` recovers `χ f`. -/
@[simp]
theorem tateLift_toTate (hC : IsAffinoidAlgebra K C) (χ : W σ →ₐ[K] C) (f : W σ) :
    tateLift hC χ (toTate σ K f) = χ f :=
  AlgHom.congr_fun (tateLift_comp_toTate hC χ) f

/-- Lift a `K`-algebra homomorphism `χ : W_σ →ₐ[K] C` vanishing on `I` to `T_σ ⧸ I T_σ →ₐ[K] C`. -/
noncomputable def tateQuotientLift (hC : IsAffinoidAlgebra K C) (I : Ideal (W σ))
    (χ : W σ →ₐ[K] C) (hI : I ≤ RingHom.ker χ) :
    (T σ ⧸ I.map (toTate σ K)) →ₐ[K] C :=
  Ideal.Quotient.liftₐ (I.map (toTate σ K)) (tateLift hC χ) fun _ hx ↦ RingHom.mem_ker.mp <|
    (Ideal.map_le_iff_le_comap.mpr fun f hf ↦ Ideal.mem_comap.mpr <|
      RingHom.mem_ker.mpr ((tateLift_toTate hC χ f).trans (RingHom.mem_ker.mp (hI hf)))) hx

/-- `tateQuotientLift` sends the class of `toTate σ K f` to `χ f`. -/
@[simp]
theorem tateQuotientLift_mk_toTate (hC : IsAffinoidAlgebra K C) (I : Ideal (W σ))
    (χ : W σ →ₐ[K] C) (hI : I ≤ RingHom.ker χ) (f : W σ) :
    tateQuotientLift hC I χ hI (Ideal.Quotient.mk (I.map (toTate σ K)) (toTate σ K f)) = χ f :=
  tateLift_toTate hC χ f

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
  have hιJ : Isometry ιJ := AddMonoidHomClass.isometry_of_norm ιJ fun x ↦ by
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.norm_mk_map_toTate J g
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

end washnitzerAlgebra

end WashnitzerAutomaticContinuity

/-! ### Functoriality and presentation-independence of the affinoid completion -/

section CompletionFunctoriality

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
  [CommRing B] [Algebra K B] [IsDaggerAlgebra K B]
  [CommRing C] [Algebra K C] [IsDaggerAlgebra K C]

/-- **Functoriality of the affinoid completion** (Grosse-Klönne, Theorem 1.7 (1)). Every
`K`-algebra homomorphism `φ : A →ₐ[K] B` of dagger algebras induces a `K`-algebra homomorphism
`φ̂ : completion K A →ₐ[K] completion K B` compatible with `toCompletion`. -/
noncomputable def completionMap (φ : A →ₐ[K] B) : completion K A →ₐ[K] completion K B :=
  washnitzerAlgebra.tateQuotientLift (K := K) (σ := Fin (presentationDim K A))
    (C := completion K B) (isAffinoidAlgebra_completion (K := K) (A := B))
    (RingHom.ker (presentation K A)) ((toCompletion K B).comp (φ.comp (presentation K A)))
    fun f hf ↦ RingHom.mem_ker.mpr (by
      rw [AlgHom.comp_apply, AlgHom.comp_apply, RingHom.mem_ker.mp hf, map_zero, map_zero])

variable {K}

/-- `completionMap K φ` commutes with `toCompletion` on elements of `A`. -/
@[simp]
theorem completionMap_toCompletion (φ : A →ₐ[K] B) (a : A) :
    completionMap K φ (toCompletion K A a) = toCompletion K B (φ a) := by
  obtain ⟨f, rfl⟩ := presentation_surjective K A a
  rw [toCompletion_presentation, completionMap, washnitzerAlgebra.tateQuotientLift_mk_toTate]
  rfl

/-- `completionMap K φ` commutes with `toCompletion` as `K`-algebra homomorphisms. -/
@[simp]
theorem completionMap_comp_toCompletion (φ : A →ₐ[K] B) :
    (completionMap K φ).comp (toCompletion K A) = (toCompletion K B).comp φ :=
  AlgHom.ext (completionMap_toCompletion φ)

/-- `completionMap K φ` is continuous. -/
theorem continuous_completionMap (φ : A →ₐ[K] B) : Continuous (completionMap K φ) :=
  have := (isAffinoidAlgebra_completion (K := K) (A := A)).isNoetherianRing
  IsAffinoidAlgebra.continuous_algHom (K := K) (A := completion K B) (B := completion K A)
    (isAffinoidAlgebra_completion (K := K) (A := B)) (completionMap K φ)

/-- **Uniqueness of the completed morphism.** `completionMap K φ` is the unique `K`-algebra
homomorphism `completion K A →ₐ[K] completion K B` commuting with `toCompletion`, with no
continuity assumption on `ψ`. -/
theorem eq_completionMap {φ : A →ₐ[K] B} {ψ : completion K A →ₐ[K] completion K B}
    (hψ : ψ.comp (toCompletion K A) = (toCompletion K B).comp φ) :
    ψ = completionMap K φ := by
  have := (isAffinoidAlgebra_completion (K := K) (A := A)).isNoetherianRing
  apply AlgHom.coe_fn_injective
  exact denseRange_toCompletion.equalizer
    (IsAffinoidAlgebra.continuous_algHom (K := K) (A := completion K B) (B := completion K A)
      (isAffinoidAlgebra_completion (K := K) (A := B)) ψ)
    (continuous_completionMap φ)
    (funext fun a ↦ (AlgHom.congr_fun hψ a).trans (completionMap_toCompletion φ a).symm)

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
  affinoidToContinuousAlgEquiv (K := K) (A := completion K A) (B := completion K B)
    (isAffinoidAlgebra_completion (K := K) (A := B)) <|
    AlgEquiv.ofAlgHom (completionMap K e.toAlgHom) (completionMap K e.symm.toAlgHom)
      (by
        rw [← completionMap_comp,
          show e.toAlgHom.comp e.symm.toAlgHom = AlgHom.id K B from AlgHom.ext e.apply_symm_apply,
          completionMap_id])
      (by
        rw [← completionMap_comp,
          show e.symm.toAlgHom.comp e.toAlgHom = AlgHom.id K A from AlgHom.ext e.symm_apply_apply,
          completionMap_id])

@[simp]
theorem completionContinuousAlgEquiv_apply (e : A ≃ₐ[K] B) (x : completion K A) :
    completionContinuousAlgEquiv K e x = completionMap K e.toAlgHom x := (rfl)

@[simp]
theorem completionContinuousAlgEquiv_symm (e : A ≃ₐ[K] B) :
    (completionContinuousAlgEquiv K e).symm = completionContinuousAlgEquiv K e.symm := by
  ext x
  rfl

@[simp]
theorem completionContinuousAlgEquiv_refl :
    completionContinuousAlgEquiv K (AlgEquiv.refl : A ≃ₐ[K] A) = ContinuousAlgEquiv.refl K _ := by
  ext x
  exact AlgHom.congr_fun completionMap_id x

end CompletionFunctoriality

/-! ### Independence of presentation for the affinoid completion and metric completion -/

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
  washnitzerAlgebra.tateQuotientLift (K := K) (σ := Fin (presentationDim K A)) (C := T σ ⧸ J)
    ((isAffinoidAlgebra_tate (K := K) (σ := σ)).quotient J)
    (RingHom.ker (presentation K A)) (τπ.comp (presentation K A))
    fun f hf ↦ RingHom.mem_ker.mpr (by rw [AlgHom.comp_apply, RingHom.mem_ker.mp hf, map_zero])

/-- **Presentation-independence of the affinoid completion.** For any surjective `K`-algebra
presentation `π : W_σ →ₐ[K] A`, the quotient `T_σ ⧸ (ker π) T_σ` is canonically isomorphic as a
topological `K`-algebra to `completion K A`, compatibly with `π` and `toCompletion`. -/
noncomputable def presentationCompletionEquiv (π : W σ →ₐ[K] A) (hπ : Function.Surjective π) :
    (T σ ⧸ (RingHom.ker π).map (washnitzerAlgebra.toTate σ K)) ≃A[K] completion K A := by
  let J : Ideal (T σ) := (RingHom.ker π).map (washnitzerAlgebra.toTate σ K)
  have hQ : IsAffinoidAlgebra K (T σ ⧸ J) := (isAffinoidAlgebra_tate (K := K) (σ := σ)).quotient J
  have := (isAffinoidAlgebra_completion (K := K) (A := A)).isNoetherianRing
  have := hQ.isNoetherianRing
  let fwd := presentationToCompletion π
  let bwd := completionToPresentation π hπ
  have hfwd (f : W σ) :
      fwd (Ideal.Quotient.mk J (washnitzerAlgebra.toTate σ K f)) = toCompletion K A (π f) :=
    washnitzerAlgebra.tateQuotientLift_mk_toTate _ _ _ _ f
  have hbwd (g : W (Fin (presentationDim K A))) (f : W σ) (hfg : π f = presentation K A g) :
      bwd (toCompletion K A (presentation K A g)) =
        Ideal.Quotient.mk J (washnitzerAlgebra.toTate σ K f) := by
    dsimp only [bwd]
    rw [toCompletion_presentation, completionToPresentation,
      washnitzerAlgebra.tateQuotientLift_mk_toTate]
    simp [J, ← hfg]
  have hfb : fwd.comp bwd = AlgHom.id K (completion K A) := by
    apply AlgHom.coe_fn_injective
    refine denseRange_toCompletion.equalizer
      (IsAffinoidAlgebra.continuous_algHom (K := K) (A := completion K A) (B := completion K A)
        (isAffinoidAlgebra_completion (K := K) (A := A)) (fwd.comp bwd))
      continuous_id (funext fun a ↦ ?_)
    obtain ⟨g, rfl⟩ := presentation_surjective K A a
    obtain ⟨f, hf⟩ := hπ (presentation K A g)
    rw [Function.comp_apply, Function.comp_apply, AlgHom.comp_apply, AlgHom.id_apply, hbwd g f hf,
      hfwd, hf]
  have hbf : bwd.comp fwd = AlgHom.id K (T σ ⧸ J) := by
    have hd : DenseRange (fun f : W σ ↦ Ideal.Quotient.mk J (washnitzerAlgebra.toTate σ K f)) :=
      Ideal.Quotient.mk_surjective.denseRange.comp washnitzerAlgebra.denseRange_toTate
        continuous_quot_mk
    apply AlgHom.coe_fn_injective
    refine hd.equalizer
      (IsAffinoidAlgebra.continuous_algHom (K := K) (A := T σ ⧸ J) (B := T σ ⧸ J) hQ (bwd.comp fwd))
      continuous_id (funext fun f ↦ ?_)
    obtain ⟨g, hg⟩ := presentation_surjective K A (π f)
    rw [Function.comp_apply, Function.comp_apply, AlgHom.comp_apply, AlgHom.id_apply, hfwd, ← hg,
      hbwd g f hg.symm]
  exact affinoidToContinuousAlgEquiv (K := K) (A := T σ ⧸ J) (B := completion K A)
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
    affinoidToContinuousAlgEquiv (K := K)
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
    affinoidToContinuousAlgEquiv (K := K)
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

variable (K A) in
/-- **Metric completion comparison** (Grosse-Klönne, Proposition 1.6 (1)). With the residue norm
`residueNormedCommRing K A`, the metric completion `UniformSpace.Completion A` is isomorphic as a
`K`-algebra to `completion K A`. -/
noncomputable def residueCompletionAlgEquiv :
    letI := residueNormedCommRing K A
    letI := residueNormedAlgebra K A
    Completion A ≃ₐ[K] completion K A :=
  letI := residueNormedCommRing K A
  letI := residueNormedAlgebra K A
  AlgHom.completionAlgEquiv (R := K) (A := A) (B := completion K A)
    (toCompletion K A) (isometry_toCompletion K A) denseRange_toCompletion

@[simp↓]
theorem residueCompletionAlgEquiv_coe (a : A) :
    letI := residueNormedCommRing K A
    letI := residueNormedAlgebra K A
    residueCompletionAlgEquiv K A (a : Completion A) = toCompletion K A a :=
  letI := residueNormedCommRing K A
  letI := residueNormedAlgebra K A
  by
    exact AlgHom.completionAlgEquiv_coe (R := K) (A := A) (B := completion K A)
      (toCompletion K A) (isometry_toCompletion K A) denseRange_toCompletion a

@[simp↓]
theorem residueCompletionAlgEquiv_symm_toCompletion (a : A) :
    letI := residueNormedCommRing K A
    letI := residueNormedAlgebra K A
    (residueCompletionAlgEquiv K A).symm (toCompletion K A a) = (a : Completion A) :=
  letI := residueNormedCommRing K A
  letI := residueNormedAlgebra K A
  by
    exact AlgHom.completionAlgEquiv_symm_apply (R := K) (A := A) (B := completion K A)
      (toCompletion K A) (isometry_toCompletion K A) denseRange_toCompletion a

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

@[simp]
theorem presentationContinuousAlgEquiv_symm_apply {D : Type*} [CommRing D] [Algebra K D]
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
  have hι : Isometry ιI := AddMonoidHomClass.isometry_of_norm ιI fun x ↦ by
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.norm_mk_map_toTate I f
  have h : ⇑(completionQuotientEquiv I) ∘ ⇑(toCompletion K (W σ ⧸ I)) = ⇑ιI := by
    funext x
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact completionQuotientEquiv_toCompletion_mk I f
  exact (completionQuotientEquiv I).toHomeomorph.isEmbedding.of_comp_iff.mp (h ▸ hι.isEmbedding)

/-- The topology of `residueNormedCommRing K A` is induced from `completion K A` along
`toCompletion K A`. -/
theorem residueNormedCommRing_toTopologicalSpace_eq_induced {A : Type*} [CommRing A] [Algebra K A]
    [IsDaggerAlgebra K A] :
    (residueNormedCommRing K A).toUniformSpace.toTopologicalSpace =
      TopologicalSpace.induced (toCompletion K A) inferInstance :=
  letI := residueNormedCommRing K A
  (isometry_toCompletion K A).isEmbedding.isInducing.eq_induced

namespace IsDaggerAlgebra

variable {A B : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
  [CommRing B] [Algebra K B] [IsDaggerAlgebra K B]

/-- **Automatic continuity of homomorphisms of dagger algebras** (general topology form). If `A`
and `B` carry the topologies induced from their affinoid completions along `toCompletion` — for
instance `W_σ`, `W_σ ⧸ I`, or `residueNormedCommRing` — then every `K`-algebra homomorphism
`φ : A →ₐ[K] B` is continuous. -/
theorem continuous_algHom_of_isInducing [TopologicalSpace A] [TopologicalSpace B]
    (hA : Topology.IsInducing (toCompletion K A)) (hB : Topology.IsInducing (toCompletion K B))
    (φ : A →ₐ[K] B) : Continuous φ := by
  rw [hB.continuous_iff]
  have hcomp : ⇑(toCompletion K B) ∘ ⇑φ = ⇑(completionMap K φ) ∘ ⇑(toCompletion K A) :=
    funext fun a ↦ (completionMap_toCompletion φ a).symm
  rw [hcomp]
  exact (continuous_completionMap φ).comp hA.continuous

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

/-- Every `K`-algebra homomorphism `φ : A →ₐ[K] B` is uniformly continuous for the residue norms. -/
theorem uniformContinuous_algHom (φ : A →ₐ[K] B) :
    letI := residueNormedCommRing K A
    letI := residueNormedCommRing K B
    UniformContinuous φ :=
  letI := residueNormedCommRing K A
  letI := residueNormedCommRing K B
  uniformContinuous_addMonoidHom_of_continuous (continuous_algHom φ)

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
    hA.eq_induced.trans (residueNormedCommRing_toTopologicalSpace_eq_induced (K := K) (A := A)).symm
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

/-- Every `K`-algebra homomorphism of dagger algebras maps power-bounded elements to power-bounded
elements (for the canonical topologies induced from `toCompletion`). -/
theorem isPowerBounded_map [TopologicalSpace A] [TopologicalSpace B]
    (hA : Topology.IsInducing (toCompletion K A)) (hB : Topology.IsInducing (toCompletion K B))
    (φ : A →ₐ[K] B) {a : A} (ha : Huber.IsPowerBounded a) :
    Huber.IsPowerBounded (φ a) := by
  have := (isAffinoidAlgebra_completion (K := K) (A := A)).isNoetherianRing
  rw [← isPowerBounded_toCompletion_iff hB, ← completionMap_toCompletion]
  exact IsAffinoidAlgebra.isPowerBounded_map (K := K) (A := completion K B) (B := completion K A)
    (isAffinoidAlgebra_completion (K := K) (A := B))
    (completionMap K φ) ((isPowerBounded_toCompletion_iff hA).mpr ha)

end IsDaggerAlgebra

section NormEquivalence

variable {A : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]

omit [CompleteSpace K] in
private theorem residueAlgEquiv_apply (a : A) :
    residueAlgEquiv K A a =
      (Ideal.quotientKerAlgEquivOfSurjective (presentation_surjective K A)).symm a := by
  obtain ⟨f, rfl⟩ := presentation_surjective K A a
  rw [residueAlgEquiv_presentation, Ideal.quotientKerAlgEquivOfSurjective_symm_apply]

/-- **Bi-Lipschitz equivalence of presentation residue norms** (Grosse-Klönne, Proposition
1.6 (2)). For any surjective presentation `π : W_σ →ₐ[K] A`, the quotient Gauss norm on
`W_σ ⧸ ker π` is bi-Lipschitz equivalent to `residueNormedCommRing K A`. -/
theorem exists_norm_presentation_equiv (π : W σ →ₐ[K] A) (hπ : Function.Surjective π) :
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
      rw [residueAlgEquiv_apply]
      exact presentationContinuousAlgEquiv_symm_apply _ (presentation_surjective K A) π hπ a
    refine ⟨?_, by rw [← he, ← norm_residueAlgEquiv]; exact hub (residueAlgEquiv K A a)⟩
    rw [inv_mul_le_iff₀ hd, ← norm_residueAlgEquiv]
    have hsymm : e.symm.toAlgHom ((Ideal.quotientKerAlgEquivOfSurjective hπ).symm a) =
        residueAlgEquiv K A a := by
      -- `e.symm.toAlgHom` evaluates identically to `e.symm`.
      change e.symm ((Ideal.quotientKerAlgEquivOfSurjective hπ).symm a) = residueAlgEquiv K A a
      rw [← he, ContinuousAlgEquiv.symm_apply_apply]
    exact hsymm ▸ hlb ((Ideal.quotientKerAlgEquivOfSurjective hπ).symm a)

/-- **Presentation-independence of the induced uniformity.** Every surjective presentation
`π : W_σ →ₐ[K] A` induces the same `UniformSpace A` as `residueNormedCommRing K A`, and hence the
same topology on `A`. -/
theorem induced_uniformSpace_presentation_eq (π : W σ →ₐ[K] A) (hπ : Function.Surjective π) :
    (NormedCommRing.induced A (W σ ⧸ RingHom.ker π)
        (Ideal.quotientKerAlgEquivOfSurjective hπ).symm
        (Ideal.quotientKerAlgEquivOfSurjective hπ).symm.injective).toUniformSpace =
      (residueNormedCommRing K A).toUniformSpace := by
  let e₁ := (Ideal.quotientKerAlgEquivOfSurjective hπ).symm
  let e₂ := residueAlgEquiv K A
  let φ := presentationContinuousAlgEquiv π hπ (presentation K A) (presentation_surjective K A)
  have hφ : ⇑φ ∘ ⇑e₁ = ⇑e₂ := funext fun a ↦
    (presentationContinuousAlgEquiv_symm_apply π hπ _ (presentation_surjective K A) a).trans
      (residueAlgEquiv_apply a).symm
  let ue : UniformEquiv (W σ ⧸ RingHom.ker π) _ :=
    { toEquiv := φ.toEquiv
      uniformContinuous_toFun := uniformContinuous_addMonoidHom_of_continuous φ.continuous
      uniformContinuous_invFun := uniformContinuous_addMonoidHom_of_continuous φ.symm.continuous }
  -- Unfold `NormedCommRing.induced.toUniformSpace` on both sides to `UniformSpace.comap`.
  change UniformSpace.comap e₁ inferInstance = UniformSpace.comap e₂ inferInstance
  rw [← hφ, UniformSpace.comap_comap]
  -- `⇑φ` and `⇑ue` are definitionally equal, allowing `UniformEquiv.comap_eq` to simplify.
  change UniformSpace.comap e₁ inferInstance = UniformSpace.comap e₁ (UniformSpace.comap ue _)
  rw [ue.comap_eq]

/-- On `W_σ`, the uniformity of `residueNormedCommRing K (W_σ)` agrees with the Gauss norm
uniformity. -/
theorem residueNormedCommRing_toUniformSpace_washnitzerAlgebra :
    (residueNormedCommRing K (W σ)).toUniformSpace = (inferInstance : UniformSpace (W σ)) := by
  rw [← induced_uniformSpace_presentation_eq (AlgHom.id K (W σ)) Function.surjective_id]
  let e := (Ideal.quotientKerAlgEquivOfSurjective
    (f := AlgHom.id K (W σ)) Function.surjective_id).symm
  have hmk (f : W σ) : e f = Ideal.Quotient.mk _ f :=
    Ideal.quotientKerAlgEquivOfSurjective_symm_apply (f := AlgHom.id K (W σ))
      Function.surjective_id f
  have he : Isometry e := AddMonoidHomClass.isometry_of_norm e fun f ↦ le_antisymm
    (hmk f ▸ Ideal.Quotient.norm_mk_le _ f) <| by
      obtain ⟨g, hg, hnorm⟩ := Ideal.exists_mk_eq_and_norm_eq_washnitzerAlgebra _ (e f)
      have hfg : g = f :=
        sub_eq_zero.mp (RingHom.mem_ker.mp (Ideal.Quotient.eq.mp (hg.trans (hmk f))))
      exact (hfg ▸ hnorm).le
  exact he.isUniformInducing.comap_uniformSpace

/-- On a presentation quotient `W_σ ⧸ I`, the uniformity of `residueNormedCommRing K (W_σ ⧸ I)`
agrees with the quotient Gauss norm uniformity. -/
theorem residueNormedCommRing_toUniformSpace_quotient (I : Ideal (W σ)) :
    (residueNormedCommRing K (W σ ⧸ I)).toUniformSpace =
      (inferInstance : UniformSpace (W σ ⧸ I)) := by
  rw [← induced_uniformSpace_presentation_eq (Ideal.Quotient.mkₐ K I)
    (Ideal.Quotient.mkₐ_surjective K I)]
  let e := (Ideal.quotientKerAlgEquivOfSurjective (Ideal.Quotient.mkₐ_surjective K I)).symm
  have he : Isometry e := AddMonoidHomClass.isometry_of_norm e fun x ↦ by
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hmk : e (Ideal.Quotient.mk I f) = Ideal.Quotient.mk _ f :=
      Ideal.quotientKerAlgEquivOfSurjective_symm_apply (Ideal.Quotient.mkₐ_surjective K I) f
    rw [hmk]
    exact congrArg (fun J : Ideal (W σ) ↦ ‖Ideal.Quotient.mk J f‖) (Ideal.Quotient.mkₐ_ker K I)
  exact he.isUniformInducing.comap_uniformSpace

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
