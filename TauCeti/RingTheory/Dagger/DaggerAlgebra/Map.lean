/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.QuotientNorm
public import TauCeti.RingTheory.Affinoid.Restricted
public import TauCeti.RingTheory.Dagger.DaggerAlgebra.Completion
public import TauCeti.RingTheory.Dagger.SupSeminorm

import TauCeti.RingTheory.Affinoid.PowerBounded
import TauCeti.RingTheory.Dagger.DaggerAlgebra.FaithfullyFlat
import TauCeti.RingTheory.Dagger.NoetherNormalization
import TauCeti.RingTheory.Dagger.Weierstrass
import TauCeti.RingTheory.Ideal.KrullIntersection

/-!
# Universal property and functoriality of the completion of a dagger algebra

Let `K` be a complete nontrivially normed ultrametric field and `A` a `K`-dagger algebra, with
completion map `τ : A → Â = completion K A`. Although `Â` is constructed from the chosen minimal
presentation `W_n ↠ A` as `T_n ⧸ I T_n`, it is characterized up to unique `K`-algebra isomorphism
under `A` by a purely algebraic universal property: `τ : A → Â` is initial among `K`-algebra
homomorphisms from `A` into `K`-affinoid algebras, with no continuity or norm assumed on the
target.

The extension of a `K`-algebra homomorphism `φ : A → S` into an affinoid algebra `S` reduces along
the presentation `W_n ↠ A` to extending a homomorphism `ψ : W_n → S` along `W_n ⊆ T_n`:

* Every classical point of `S` contracts to a classical point of `W_n`, where each coordinate
  variable `Xᵢ` has absolute value at most `‖Xᵢ‖ = 1`. Thus `|ψ Xᵢ|sup ≤ 1` in `S`, so `ψ Xᵢ` is
  power-bounded (`TauCeti.IsAffinoidAlgebra.isPowerBounded_iff_supSeminorm_le_one`) when `S` is
  equipped with a complete ultrametric algebra norm
  (`TauCeti.IsAffinoidAlgebra.residueNormedCommRing`).
* Restricted evaluation (`TauCeti.IsAffinoidAlgebra.restrictedLift`) produces a `K`-algebra
  homomorphism `Ψ : T_n → S` sending each `Xᵢ` to `ψ Xᵢ`. Because `S` is noetherian and its
  quotients `S ⧸ m ^ k` by powers of maximal ideals are finite over `K`, `Ψ ∘ toTate` and `ψ`
  agree modulo every `m ^ k` (`TauCeti.Dagger.washnitzerAlgebra.algHom_ext_of_isIntegral`), hence
  globally by Krull's intersection theorem (`Ideal.iInf_isMaximal_pow_eq_bot`).
* Uniqueness of `Φ : Â → S` with `Φ ∘ τ = φ` needs no continuity hypothesis: any such `Φ` is
  automatically continuous for `S`'s residue norm (`TauCeti.IsAffinoidAlgebra.continuous_algHom`),
  and `τ(A)` is dense in `Â` (`TauCeti.Dagger.denseRange_toCompletion`).

Specializing `S` to the completion `B̂` of a second dagger algebra `B` makes `A ↦ Â` a functor
(`TauCeti.Dagger.completionMap`) sending `K`-algebra isomorphisms to topological `K`-algebra
isomorphisms (`TauCeti.Dagger.completionContinuousAlgEquivOfAlgEquiv`). Applying the universal
property in both directions identifies `Â` with `T_σ ⧸ (ker π) T_σ` for every presentation
`π : W_σ ↠ A` (`TauCeti.Dagger.presentationCompletionContinuousAlgEquiv`), and in particular
identifies the completion of `W_σ` with `T_σ`
(`TauCeti.Dagger.washnitzerAlgebra.completionContinuousAlgEquiv`).

## Main definitions

* `TauCeti.Dagger.washnitzerAlgebra.liftToTate`: the unique `K`-algebra extension `T_σ →ₐ[K] S` of
  a homomorphism `W_σ →ₐ[K] S` into an affinoid algebra.
* `TauCeti.Dagger.completionLift`, `TauCeti.Dagger.completionLiftEquiv`: the universal extension
  `(completion K A →ₐ[K] S) ≃ (A →ₐ[K] S)` for an affinoid algebra `S`.
* `TauCeti.Dagger.completionMap`: the completion `completion K A →ₐ[K] completion K B` of a
  morphism `A →ₐ[K] B` of dagger algebras, and
  `TauCeti.Dagger.completionContinuousAlgEquivOfAlgEquiv`: the induced topological isomorphism for
  `A ≃ₐ[K] B`.
* `TauCeti.Dagger.presentationCompletionContinuousAlgEquiv`: comparison of `completion K A` with
  `T_σ ⧸ (ker π) T_σ` for an arbitrary presentation `π : W_σ ↠ A`.
* `TauCeti.Dagger.washnitzerAlgebra.completionContinuousAlgEquiv`: the topological `K`-algebra
  isomorphism `completion K (washnitzerAlgebra σ K) ≃A[K] T_σ`.

## Main results

* `TauCeti.Dagger.washnitzerAlgebra.algHom_ext_of_isAffinoidAlgebra` and
  `TauCeti.Dagger.washnitzerAlgebra.algHom_ext_of_isDaggerAlgebra`: `K`-algebra maps out of `W_σ`
  into an affinoid or dagger algebra are determined by the coordinate variables.
* `TauCeti.Dagger.existsUnique_algHom_completion`: every `K`-algebra map `A →ₐ[K] S` into an
  affinoid algebra factors uniquely through `toCompletion K A`.
* `TauCeti.Dagger.completionMap_id`, `TauCeti.Dagger.completionMap_comp`,
  `TauCeti.Dagger.continuous_completionMap`: functoriality and continuity of `completionMap`.
* `TauCeti.Dagger.supSeminorm_toCompletion`, `TauCeti.Dagger.IsDaggerAlgebra.supSeminorm_map_le`:
  the completion map preserves `supSeminorm`, and morphisms of dagger algebras contract it.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1.2 and Theorem 1.7 (1).
* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §6.1.3.

The extension and uniqueness arguments adapt the restricted-series universal property in
`TauCeti.RingTheory.Affinoid.Restricted` and automatic continuity in
`TauCeti.RingTheory.Affinoid.Continuity` from Tate algebras to Monsky–Washnitzer presentations.
-/

public section

namespace TauCeti.Dagger

open _root_.MvPowerSeries

section AlgHomExt

namespace washnitzerAlgebra

variable {K σ : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Finite σ]

/-- **Homomorphisms from `W_σ` separated by finite maximal-power quotients are determined by the
variables.** If `R` is a noetherian `K`-algebra whose quotients `R ⧸ m ^ k` by all powers of
maximal ideals are finite over `K`, then two `K`-algebra homomorphisms `W_σ →ₐ[K] R` agreeing on
every coordinate variable are equal. No continuity or norm on `R` is assumed. -/
theorem algHom_ext_of_isNoetherianRing {R : Type*} [CommRing R] [Algebra K R]
    [IsNoetherianRing R]
    (hfin : ∀ (m : Ideal R) [m.IsMaximal] (k : ℕ), Module.Finite K (R ⧸ m ^ k))
    {φ ψ : washnitzerAlgebra σ K →ₐ[K] R} (h : ∀ i, φ (X σ K i) = ψ (X σ K i)) : φ = ψ := by
  ext f
  suffices φ f - ψ f ∈ (⊥ : Ideal R) from sub_eq_zero.mp this
  rw [← Ideal.iInf_isMaximal_pow_eq_bot]
  simp only [Ideal.mem_iInf]
  intro m hm k _
  let := hm
  have := hfin m k
  have : Algebra.IsIntegral K (R ⧸ m ^ k) := Algebra.IsIntegral.of_finite K _
  let q := Ideal.Quotient.mkₐ K (m ^ k)
  have hq : q.comp φ = q.comp ψ := algHom_ext_of_isIntegral fun i ↦ by simp [h i]
  exact Ideal.Quotient.eq_zero_iff_mem.mp
    (by simpa [q, map_sub] using sub_eq_zero.mpr (AlgHom.congr_fun hq f))

/-- **`K`-algebra homomorphisms from `W_σ` into an affinoid algebra are determined by the
variables**, with no continuity assumed. -/
theorem algHom_ext_of_isAffinoidAlgebra {R : Type*} [CommRing R] [Algebra K R]
    (hR : IsAffinoidAlgebra K R) {φ ψ : washnitzerAlgebra σ K →ₐ[K] R}
    (h : ∀ i, φ (X σ K i) = ψ (X σ K i)) : φ = ψ :=
  have := hR.isNoetherianRing
  algHom_ext_of_isNoetherianRing (fun m _ k ↦ hR.finite_quotient_pow m k) h

/-- **`K`-algebra homomorphisms from `W_σ` into a dagger algebra are determined by the
variables**, with no continuity assumed. -/
theorem algHom_ext_of_isDaggerAlgebra {R : Type*} [CommRing R] [Algebra K R]
    [IsDaggerAlgebra K R] {φ ψ : washnitzerAlgebra σ K →ₐ[K] R}
    (h : ∀ i, φ (X σ K i) = ψ (X σ K i)) : φ = ψ := by
  have := IsDaggerAlgebra.isNoetherianRing (K := K) (A := R)
  refine algHom_ext_of_isNoetherianRing (fun m hm k ↦ ?_) h
  have : m.radical.IsMaximal := (Ideal.IsMaximal.isPrime hm).radical.symm ▸ hm
  exact IsDaggerAlgebra.finite_quotient_pow_of_isMaximal_radical K m k

end washnitzerAlgebra

end AlgHomExt

section UniversalProperty

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

local notation "T " σ:max => IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ))

namespace washnitzerAlgebra

variable {σ : Type*} [Finite σ]

/-- Every `K`-algebra homomorphism from `W_σ` into a completely normed affinoid algebra maps each
coordinate variable to a power-bounded element. -/
theorem isPowerBounded_map_X {S : Type*} [NormedCommRing S] [NormedAlgebra K S]
    [IsUltrametricDist S] [CompleteSpace S] (hS : IsAffinoidAlgebra K S)
    (ψ : washnitzerAlgebra σ K →ₐ[K] S) (i : σ) : Huber.IsPowerBounded (ψ (X σ K i)) := by
  rw [hS.isPowerBounded_iff_supSeminorm_le_one]
  refine supSeminorm_le zero_le_one fun x ↦ ?_
  rw [← hS.pointNorm_maximalSpectrumComap ψ x]
  exact (pointNorm_le_norm _ (X σ K i)).trans_eq (norm_X i)

/-- Two `K`-algebra homomorphisms from the Tate algebra `T_σ` into an affinoid algebra that agree on
`W_σ` are equal. No norm or continuity on the target is required. -/
theorem tate_algHom_ext_of_isAffinoidAlgebra {S : Type*} [CommRing S] [Algebra K S]
    (hS : IsAffinoidAlgebra K S) {Φ₁ Φ₂ : T σ →ₐ[K] S}
    (h : ∀ f, Φ₁ (toTate σ K f) = Φ₂ (toTate σ K f)) : Φ₁ = Φ₂ := by
  let := hS.residueNormedCommRing
  let := hS.residueNormedAlgebra
  have := hS.isUltrametricDist_residueNormedCommRing
  have := hS.completeSpace_residueNormedCommRing
  have := (isAffinoidAlgebra_tate (K := K) (σ := σ)).isNoetherianRing
  exact AlgHom.coe_fn_injective <|
    denseRange_toTate.equalizer (hS.continuous_algHom (B := T σ) Φ₁)
      (hS.continuous_algHom (B := T σ) Φ₂) (funext h)

/-- **Extension of homomorphisms along `W_σ ⊆ T_σ`.** Every `K`-algebra homomorphism
`ψ : W_σ →ₐ[K] S` into an affinoid algebra extends to a `K`-algebra homomorphism `T_σ →ₐ[K] S`. -/
noncomputable def liftToTate {S : Type*} [CommRing S] [Algebra K S] (hS : IsAffinoidAlgebra K S)
    (ψ : washnitzerAlgebra σ K →ₐ[K] S) : T σ →ₐ[K] S :=
  letI := Fintype.ofFinite σ
  letI := hS.residueNormedCommRing
  letI := hS.residueNormedAlgebra
  haveI := hS.isUltrametricDist_residueNormedCommRing
  haveI := hS.completeSpace_residueNormedCommRing
  let e := Fintype.equivFin σ
  (isAffinoidAlgebra_self.restrictedLift hS (Algebra.ofId K S)
    (b := fun j ↦ ψ (X σ K (e.symm j)))
    (fun j ↦ isPowerBounded_map_X hS ψ (e.symm j))).comp
    (IsRestricted.renameAlgEquiv e (fun _ ↦ (1 : ℝ))).toAlgHom

/-- `liftToTate` sends each variable `Xᵢ` of `T_σ` to `ψ (Xᵢ)`. -/
@[simp]
theorem liftToTate_X {S : Type*} [CommRing S] [Algebra K S] (hS : IsAffinoidAlgebra K S)
    (ψ : washnitzerAlgebra σ K →ₐ[K] S) (i : σ) :
    liftToTate hS ψ ⟨_root_.MvPowerSeries.X i, isRestricted_X _ i⟩ = ψ (X σ K i) := by
  let := Fintype.ofFinite σ
  let := hS.residueNormedCommRing
  let := hS.residueNormedAlgebra
  have := hS.isUltrametricDist_residueNormedCommRing
  have := hS.completeSpace_residueNormedCommRing
  let e := Fintype.equivFin σ
  have hren := IsRestricted.renameAlgEquiv_X (R := K) e (fun _ ↦ (1 : ℝ)) i
  simp [liftToTate, e, hren]

/-- `liftToTate` restricts to `ψ` along `toTate`. -/
@[simp]
theorem liftToTate_comp_toTate {S : Type*} [CommRing S] [Algebra K S] (hS : IsAffinoidAlgebra K S)
    (ψ : washnitzerAlgebra σ K →ₐ[K] S) : (liftToTate hS ψ).comp (toTate σ K) = ψ := by
  refine algHom_ext_of_isAffinoidAlgebra hS fun i ↦ ?_
  have hX : toTate σ K (X σ K i) = ⟨_root_.MvPowerSeries.X i, isRestricted_X _ i⟩ :=
    Subtype.ext (by simp)
  simp [hX]

/-- `liftToTate` agrees with `ψ` on every overconvergent series. -/
@[simp]
theorem liftToTate_toTate {S : Type*} [CommRing S] [Algebra K S] (hS : IsAffinoidAlgebra K S)
    (ψ : washnitzerAlgebra σ K →ₐ[K] S) (f : washnitzerAlgebra σ K) :
    liftToTate hS ψ (toTate σ K f) = ψ f :=
  AlgHom.congr_fun (liftToTate_comp_toTate hS ψ) f

/-- **Universal property of `toTate`.** Every `K`-algebra homomorphism from `W_σ` into an affinoid
algebra extends uniquely along `W_σ → T_σ`. -/
theorem existsUnique_algHom_toTate {S : Type*} [CommRing S] [Algebra K S]
    (hS : IsAffinoidAlgebra K S) (ψ : washnitzerAlgebra σ K →ₐ[K] S) :
    ∃! Φ : T σ →ₐ[K] S, Φ.comp (toTate σ K) = ψ :=
  ⟨liftToTate hS ψ, liftToTate_comp_toTate hS ψ, fun _ hΦ ↦
    tate_algHom_ext_of_isAffinoidAlgebra hS fun f ↦ by
      rw [← AlgHom.comp_apply, hΦ, liftToTate_toTate]⟩

end washnitzerAlgebra

section CompletionLift

variable {A S : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
  [CommRing S] [Algebra K S]

/-- Two `K`-algebra homomorphisms out of `completion K A` into an affinoid algebra that agree on
`toCompletion K A` are equal. No continuity or norm on `S` is assumed. -/
theorem completion_algHom_ext_of_isAffinoidAlgebra (hS : IsAffinoidAlgebra K S)
    {Φ₁ Φ₂ : completion K A →ₐ[K] S}
    (h : ∀ a, Φ₁ (toCompletion K A a) = Φ₂ (toCompletion K A a)) : Φ₁ = Φ₂ := by
  let := hS.residueNormedCommRing
  let := hS.residueNormedAlgebra
  have := hS.isUltrametricDist_residueNormedCommRing
  have := hS.completeSpace_residueNormedCommRing
  have := (isAffinoidAlgebra_completion (K := K) (A := A)).isNoetherianRing
  exact AlgHom.coe_fn_injective <|
    denseRange_toCompletion.equalizer (hS.continuous_algHom (B := completion K A) Φ₁)
      (hS.continuous_algHom (B := completion K A) Φ₂) (funext h)

/-- **Universal extension to the completion.** Every `K`-algebra homomorphism `φ : A →ₐ[K] S` from
a dagger algebra into an affinoid algebra extends across `toCompletion K A : A →ₐ[K] completion K A`
to a `K`-algebra homomorphism `completion K A →ₐ[K] S`. -/
noncomputable def completionLift (hS : IsAffinoidAlgebra K S) (φ : A →ₐ[K] S) :
    completion K A →ₐ[K] S :=
  let liftT := washnitzerAlgebra.liftToTate hS (φ.comp (presentation K A))
  have hker : (RingHom.ker (presentation K A)).map (washnitzerAlgebra.toTate _ K) ≤
      RingHom.ker liftT :=
    Ideal.map_le_iff_le_comap.mpr fun f hf ↦ by
      rw [Ideal.mem_comap, RingHom.mem_ker, washnitzerAlgebra.liftToTate_toTate,
        AlgHom.comp_apply, RingHom.mem_ker.mp hf, map_zero]
  Ideal.Quotient.liftₐ _ liftT fun _ hx ↦ RingHom.mem_ker.mp (hker hx)

/-- `completionLift` extends `φ` on every element of `A`. -/
@[simp]
theorem completionLift_toCompletion (hS : IsAffinoidAlgebra K S) (φ : A →ₐ[K] S) (a : A) :
    completionLift hS φ (toCompletion K A a) = φ a := by
  obtain ⟨f, rfl⟩ := presentation_surjective K A a
  rw [toCompletion_presentation]
  exact (Ideal.Quotient.lift_mk _ _ _).trans
    (washnitzerAlgebra.liftToTate_toTate hS (φ.comp (presentation K A)) f)

/-- Precomposing `completionLift` with `toCompletion` recovers `φ`. -/
@[simp]
theorem completionLift_comp_toCompletion (hS : IsAffinoidAlgebra K S) (φ : A →ₐ[K] S) :
    (completionLift hS φ).comp (toCompletion K A) = φ :=
  AlgHom.ext (completionLift_toCompletion hS φ)

/-- **Universal property of the completion of a dagger algebra.** For every `K`-affinoid algebra `S`
and `K`-algebra homomorphism `φ : A →ₐ[K] S`, there is a unique `K`-algebra homomorphism
`Φ : completion K A →ₐ[K] S` with `Φ ∘ toCompletion K A = φ`. -/
theorem existsUnique_algHom_completion (hS : IsAffinoidAlgebra K S) (φ : A →ₐ[K] S) :
    ∃! Φ : completion K A →ₐ[K] S, Φ.comp (toCompletion K A) = φ :=
  ⟨completionLift hS φ, completionLift_comp_toCompletion hS φ, fun _ hΦ ↦
    completion_algHom_ext_of_isAffinoidAlgebra hS fun a ↦ by
      rw [← AlgHom.comp_apply, hΦ, completionLift_toCompletion]⟩

/-- Precomposition with `toCompletion K A` identifies `K`-algebra homomorphisms
`completion K A →ₐ[K] S` into an affinoid algebra with `K`-algebra homomorphisms `A →ₐ[K] S`. -/
noncomputable def completionLiftEquiv (hS : IsAffinoidAlgebra K S) :
    (completion K A →ₐ[K] S) ≃ (A →ₐ[K] S) where
  toFun Φ := Φ.comp (toCompletion K A)
  invFun := completionLift hS
  left_inv Φ := completion_algHom_ext_of_isAffinoidAlgebra hS
    (completionLift_toCompletion hS (Φ.comp (toCompletion K A)))
  right_inv := completionLift_comp_toCompletion hS

/-- Applying `completionLiftEquiv` precomposes with `toCompletion K A`. -/
@[simp]
theorem completionLiftEquiv_apply (hS : IsAffinoidAlgebra K S) (Φ : completion K A →ₐ[K] S) :
    completionLiftEquiv hS Φ = Φ.comp (toCompletion K A) := (rfl)

/-- The inverse of `completionLiftEquiv` is `completionLift`. -/
@[simp]
theorem completionLiftEquiv_symm_apply (hS : IsAffinoidAlgebra K S) (φ : A →ₐ[K] S) :
    (completionLiftEquiv hS).symm φ = completionLift hS φ := (rfl)

end CompletionLift

end UniversalProperty

section Functoriality

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
  [CommRing B] [Algebra K B] [IsDaggerAlgebra K B]
  [CommRing C] [Algebra K C] [IsDaggerAlgebra K C]

/-- Two `K`-algebra homomorphisms between completions of dagger algebras that agree on `A` are
equal. -/
theorem completion_algHom_ext {Φ₁ Φ₂ : completion K A →ₐ[K] completion K B}
    (h : ∀ a, Φ₁ (toCompletion K A a) = Φ₂ (toCompletion K A a)) : Φ₁ = Φ₂ :=
  completion_algHom_ext_of_isAffinoidAlgebra isAffinoidAlgebra_completion h

/-- **Functoriality of dagger completion.** Every `K`-algebra homomorphism `φ : A →ₐ[K] B` of
dagger algebras extends uniquely to a `K`-algebra homomorphism
`φ̂ : completion K A →ₐ[K] completion K B` compatible with `toCompletion`. -/
noncomputable def completionMap (φ : A →ₐ[K] B) : completion K A →ₐ[K] completion K B :=
  completionLift isAffinoidAlgebra_completion ((toCompletion K B).comp φ)

/-- `completionMap φ` commutes with `toCompletion` on elements. -/
@[simp]
theorem completionMap_toCompletion (φ : A →ₐ[K] B) (a : A) :
    completionMap φ (toCompletion K A a) = toCompletion K B (φ a) :=
  completionLift_toCompletion isAffinoidAlgebra_completion _ a

/-- `completionMap φ` intertwines the completion maps. -/
@[simp]
theorem completionMap_comp_toCompletion (φ : A →ₐ[K] B) :
    (completionMap φ).comp (toCompletion K A) = (toCompletion K B).comp φ :=
  completionLift_comp_toCompletion isAffinoidAlgebra_completion _

/-- `completionMap φ` is the unique `K`-algebra homomorphism `Â →ₐ[K] B̂` intertwining `φ` with
`toCompletion`. -/
theorem completionMap_unique {φ : A →ₐ[K] B} {Φ : completion K A →ₐ[K] completion K B}
    (h : Φ.comp (toCompletion K A) = (toCompletion K B).comp φ) : Φ = completionMap φ :=
  completion_algHom_ext fun a ↦ by
    rw [← AlgHom.comp_apply, h, AlgHom.comp_apply, completionMap_toCompletion]

/-- The induced map between completions is continuous for their quotient Gauss norms. -/
theorem continuous_completionMap (φ : A →ₐ[K] B) : Continuous (completionMap φ) :=
  have := (isAffinoidAlgebra_completion (K := K) (A := A)).isNoetherianRing
  IsAffinoidAlgebra.continuous_algHom (K := K) (A := completion K B) (B := completion K A)
    isAffinoidAlgebra_completion (completionMap φ)

/-- `completionMap` sends the identity homomorphism to the identity homomorphism. -/
@[simp]
theorem completionMap_id :
    completionMap (AlgHom.id K A) = AlgHom.id K (completion K A) :=
  completion_algHom_ext fun a ↦ by simp

/-- `completionMap` respects composition of `K`-algebra homomorphisms. -/
@[simp]
theorem completionMap_comp (ψ : B →ₐ[K] C) (φ : A →ₐ[K] B) :
    completionMap (ψ.comp φ) = (completionMap ψ).comp (completionMap φ) :=
  completion_algHom_ext fun a ↦ by simp

/-- A `K`-algebra isomorphism of dagger algebras induces a `K`-algebra isomorphism of their
completions. -/
noncomputable def completionAlgEquivOfAlgEquiv (e : A ≃ₐ[K] B) :
    completion K A ≃ₐ[K] completion K B :=
  AlgEquiv.ofAlgHom (completionMap e.toAlgHom) (completionMap e.symm.toAlgHom)
    (completion_algHom_ext fun b ↦ by simp)
    (completion_algHom_ext fun a ↦ by simp)

/-- The underlying `AlgHom` of `completionAlgEquivOfAlgEquiv e` is `completionMap e.toAlgHom`. -/
@[simp]
theorem toAlgHom_completionAlgEquivOfAlgEquiv (e : A ≃ₐ[K] B) :
    (completionAlgEquivOfAlgEquiv e).toAlgHom = completionMap e.toAlgHom := (rfl)

/-- Applying `completionAlgEquivOfAlgEquiv e` evaluates `completionMap e.toAlgHom`. -/
@[simp]
theorem completionAlgEquivOfAlgEquiv_apply (e : A ≃ₐ[K] B) (x : completion K A) :
    completionAlgEquivOfAlgEquiv e x = completionMap e.toAlgHom x := (rfl)

/-- `completionAlgEquivOfAlgEquiv` commutes with `.symm`. -/
@[simp]
theorem completionAlgEquivOfAlgEquiv_symm (e : A ≃ₐ[K] B) :
    (completionAlgEquivOfAlgEquiv e).symm = completionAlgEquivOfAlgEquiv e.symm := (rfl)

/-- A `K`-algebra isomorphism of dagger algebras induces a topological `K`-algebra isomorphism of
their completions. -/
noncomputable def completionContinuousAlgEquivOfAlgEquiv (e : A ≃ₐ[K] B) :
    completion K A ≃A[K] completion K B :=
  IsAffinoidAlgebra.toContinuousAlgEquiv (K := K) (A := completion K A) (B := completion K B)
    isAffinoidAlgebra_completion (completionAlgEquivOfAlgEquiv e)

/-- The underlying `AlgEquiv` of `completionContinuousAlgEquivOfAlgEquiv e` is
`completionAlgEquivOfAlgEquiv e`. -/
@[simp]
theorem toAlgEquiv_completionContinuousAlgEquivOfAlgEquiv (e : A ≃ₐ[K] B) :
    (completionContinuousAlgEquivOfAlgEquiv e).toAlgEquiv = completionAlgEquivOfAlgEquiv e := by
  simp [completionContinuousAlgEquivOfAlgEquiv]

/-- Applying `completionContinuousAlgEquivOfAlgEquiv e` evaluates `completionMap e.toAlgHom`. -/
@[simp]
theorem completionContinuousAlgEquivOfAlgEquiv_apply (e : A ≃ₐ[K] B) (x : completion K A) :
    completionContinuousAlgEquivOfAlgEquiv e x = completionMap e.toAlgHom x := by
  simp [completionContinuousAlgEquivOfAlgEquiv]

/-- `completionContinuousAlgEquivOfAlgEquiv e` commutes with `toCompletion`. -/
theorem completionContinuousAlgEquivOfAlgEquiv_toCompletion (e : A ≃ₐ[K] B) (a : A) :
    completionContinuousAlgEquivOfAlgEquiv e (toCompletion K A a) = toCompletion K B (e a) := by
  simp

/-- `completionContinuousAlgEquivOfAlgEquiv` commutes with `.symm`. -/
@[simp]
theorem completionContinuousAlgEquivOfAlgEquiv_symm (e : A ≃ₐ[K] B) :
    (completionContinuousAlgEquivOfAlgEquiv e).symm =
      completionContinuousAlgEquivOfAlgEquiv e.symm := by
  ext x
  refine (completionContinuousAlgEquivOfAlgEquiv e).symm_apply_eq.mpr ?_
  have h : completionMap e.toAlgHom (completionMap e.symm.toAlgHom x) = x := by
    simp [← AlgHom.comp_apply, ← completionMap_comp]
  simpa using h.symm

/-- `completionContinuousAlgEquivOfAlgEquiv` sends `AlgEquiv.refl` to `ContinuousAlgEquiv.refl`. -/
@[simp]
theorem completionContinuousAlgEquivOfAlgEquiv_refl :
    completionContinuousAlgEquivOfAlgEquiv (AlgEquiv.refl : A ≃ₐ[K] A) =
      ContinuousAlgEquiv.refl K (completion K A) := by
  ext x
  simp

/-- `completionContinuousAlgEquivOfAlgEquiv` respects composition of `K`-algebra isomorphisms. -/
@[simp]
theorem completionContinuousAlgEquivOfAlgEquiv_trans (e₁ : A ≃ₐ[K] B) (e₂ : B ≃ₐ[K] C) :
    completionContinuousAlgEquivOfAlgEquiv (e₁.trans e₂) =
      (completionContinuousAlgEquivOfAlgEquiv e₁).trans
        (completionContinuousAlgEquivOfAlgEquiv e₂) := by
  ext x
  have h : (e₁.trans e₂).toAlgHom = e₂.toAlgHom.comp e₁.toAlgHom := rfl
  simp [h]

end Functoriality

section PresentationComparison

section ArbitraryPresentation

variable {K σ : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Finite σ] {A : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]

local notation "T " σ:max => IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ))

/-- The canonical `K`-algebra map `A → T_σ ⧸ (ker π) T_σ` attached to an arbitrary surjective
presentation `π : W_σ ↠ A`. -/
private noncomputable def toPresentationCompletion (π : washnitzerAlgebra σ K →ₐ[K] A)
    (hπ : Function.Surjective π) :
    A →ₐ[K] T σ ⧸ (RingHom.ker π).map (washnitzerAlgebra.toTate σ K) :=
  (Ideal.quotientMapₐ _ (washnitzerAlgebra.toTate σ K) Ideal.le_comap_map).comp
    (Ideal.quotientKerAlgEquivOfSurjective hπ).symm.toAlgHom

omit [CompleteSpace K] [Finite σ] [IsDaggerAlgebra K A] in
@[simp]
private theorem toPresentationCompletion_apply (π : washnitzerAlgebra σ K →ₐ[K] A)
    (hπ : Function.Surjective π) (f : washnitzerAlgebra σ K) :
    toPresentationCompletion π hπ (π f) =
      Ideal.Quotient.mk _ (washnitzerAlgebra.toTate σ K f) := by
  simp [toPresentationCompletion]

/-- **Presentation independence of the completion.** For any surjective presentation
`π : W_σ →ₐ[K] A` of a dagger algebra, `completion K A` is canonically topologically isomorphic as
a `K`-algebra to `T_σ ⧸ (ker π) T_σ` under `A`. -/
noncomputable def presentationCompletionContinuousAlgEquiv
    (π : washnitzerAlgebra σ K →ₐ[K] A) (hπ : Function.Surjective π) :
    completion K A ≃A[K] T σ ⧸ (RingHom.ker π).map (washnitzerAlgebra.toTate σ K) :=
  have hQ : IsAffinoidAlgebra K (T σ ⧸ (RingHom.ker π).map (washnitzerAlgebra.toTate σ K)) :=
    isAffinoidAlgebra_tate.quotient _
  have := hQ.isNoetherianRing
  let fwd : completion K A →ₐ[K] T σ ⧸ (RingHom.ker π).map (washnitzerAlgebra.toTate σ K) :=
    completionLift hQ (toPresentationCompletion π hπ)
  let liftT : T σ →ₐ[K] completion K A :=
    washnitzerAlgebra.liftToTate isAffinoidAlgebra_completion ((toCompletion K A).comp π)
  have hker : (RingHom.ker π).map (washnitzerAlgebra.toTate σ K) ≤ RingHom.ker liftT :=
    Ideal.map_le_iff_le_comap.mpr fun f hf ↦ by
      rw [Ideal.mem_comap, RingHom.mem_ker, washnitzerAlgebra.liftToTate_toTate,
        AlgHom.comp_apply, RingHom.mem_ker.mp hf, map_zero]
  let bwd : (T σ ⧸ (RingHom.ker π).map (washnitzerAlgebra.toTate σ K)) →ₐ[K] completion K A :=
    Ideal.Quotient.liftₐ _ liftT fun _ hx ↦ RingHom.mem_ker.mp (hker hx)
  have hbwd_mk (f : washnitzerAlgebra σ K) :
      bwd (Ideal.Quotient.mk _ (washnitzerAlgebra.toTate σ K f)) = toCompletion K A (π f) :=
    (Ideal.Quotient.lift_mk _ _ _).trans
      (washnitzerAlgebra.liftToTate_toTate isAffinoidAlgebra_completion
        ((toCompletion K A).comp π) f)
  have hbf : bwd.comp fwd = AlgHom.id K (completion K A) :=
    completion_algHom_ext fun a ↦ by
      obtain ⟨f, rfl⟩ := hπ a
      simp [fwd, hbwd_mk]
  have hdense : DenseRange
      (Ideal.Quotient.mk ((RingHom.ker π).map (washnitzerAlgebra.toTate σ K)) ∘
        washnitzerAlgebra.toTate σ K) :=
    Ideal.Quotient.mk_surjective.denseRange.comp washnitzerAlgebra.denseRange_toTate
      continuous_quot_mk
  have hfb : fwd.comp bwd = AlgHom.id K _ :=
    AlgHom.coe_fn_injective <|
      hdense.equalizer
        (IsAffinoidAlgebra.continuous_algHom (K := K)
          (A := T σ ⧸ (RingHom.ker π).map (washnitzerAlgebra.toTate σ K))
          (B := T σ ⧸ (RingHom.ker π).map (washnitzerAlgebra.toTate σ K))
          hQ (fwd.comp bwd))
        continuous_id <|
        funext fun f ↦ by simp [fwd, hbwd_mk]
  IsAffinoidAlgebra.toContinuousAlgEquiv (K := K) (A := completion K A)
    (B := T σ ⧸ (RingHom.ker π).map (washnitzerAlgebra.toTate σ K)) hQ
    (AlgEquiv.ofAlgHom fwd bwd hfb hbf)

/-- `presentationCompletionContinuousAlgEquiv` sends `toCompletion K A (π f)` to the class of
`toTate σ K f`. -/
@[simp]
theorem presentationCompletionContinuousAlgEquiv_toCompletion
    (π : washnitzerAlgebra σ K →ₐ[K] A) (hπ : Function.Surjective π)
    (f : washnitzerAlgebra σ K) :
    presentationCompletionContinuousAlgEquiv π hπ (toCompletion K A (π f)) =
      Ideal.Quotient.mk _ (washnitzerAlgebra.toTate σ K f) := by
  simp [presentationCompletionContinuousAlgEquiv]

/-- The inverse of `presentationCompletionContinuousAlgEquiv` sends the class of `toTate σ K f` to
`toCompletion K A (π f)`. -/
@[simp]
theorem presentationCompletionContinuousAlgEquiv_symm_mk_toTate
    (π : washnitzerAlgebra σ K →ₐ[K] A) (hπ : Function.Surjective π)
    (f : washnitzerAlgebra σ K) :
    (presentationCompletionContinuousAlgEquiv π hπ).symm
      (Ideal.Quotient.mk _ (washnitzerAlgebra.toTate σ K f)) =
      toCompletion K A (π f) :=
  (presentationCompletionContinuousAlgEquiv π hπ).symm_apply_eq.mpr
    (presentationCompletionContinuousAlgEquiv_toCompletion π hπ f).symm

end ArbitraryPresentation

namespace washnitzerAlgebra

variable {σ K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Finite σ]

local notation "T" => IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ))

variable (σ K) in
/-- **The completion of the Monsky–Washnitzer algebra is the Tate algebra.** The completion
`completion K (washnitzerAlgebra σ K)` is canonically topologically isomorphic as a `K`-algebra to
`T_σ = K⟨X⟩`, compatibly with `toCompletion` and `toTate`. -/
noncomputable def completionContinuousAlgEquiv :
    completion K (washnitzerAlgebra σ K) ≃A[K] T :=
  have := (isAffinoidAlgebra_tate (K := K) (σ := σ)).isNoetherianRing
  let fwd : completion K (washnitzerAlgebra σ K) →ₐ[K] T :=
    completionLift isAffinoidAlgebra_tate (toTate σ K)
  let bwd : T →ₐ[K] completion K (washnitzerAlgebra σ K) :=
    liftToTate isAffinoidAlgebra_completion (toCompletion K (washnitzerAlgebra σ K))
  have hbf : bwd.comp fwd = AlgHom.id K _ := completion_algHom_ext fun f ↦ by simp [fwd, bwd]
  have hfb : fwd.comp bwd = AlgHom.id K _ :=
    tate_algHom_ext_of_isAffinoidAlgebra isAffinoidAlgebra_tate fun f ↦ by simp [fwd, bwd]
  IsAffinoidAlgebra.toContinuousAlgEquiv (K := K)
    (A := completion K (washnitzerAlgebra σ K)) (B := T) isAffinoidAlgebra_tate
    (AlgEquiv.ofAlgHom fwd bwd hfb hbf)

/-- The completion comparison on `W_σ` intertwines `toCompletion` with `toTate`. -/
@[simp]
theorem completionContinuousAlgEquiv_toCompletion (f : washnitzerAlgebra σ K) :
    completionContinuousAlgEquiv σ K (toCompletion K (washnitzerAlgebra σ K) f) =
      toTate σ K f := by
  simp [completionContinuousAlgEquiv]

/-- The inverse completion comparison on `W_σ` sends `toTate σ K f` to `toCompletion K W_σ f`. -/
@[simp]
theorem completionContinuousAlgEquiv_symm_toTate (f : washnitzerAlgebra σ K) :
    (completionContinuousAlgEquiv σ K).symm (toTate σ K f) =
      toCompletion K (washnitzerAlgebra σ K) f :=
  (completionContinuousAlgEquiv σ K).symm_apply_eq.mpr
    (completionContinuousAlgEquiv_toCompletion f).symm

/-- On coordinate variables, `completionContinuousAlgEquiv` sends `toCompletion (Xᵢ)` to `Xᵢ`. -/
theorem completionContinuousAlgEquiv_X (i : σ) :
    completionContinuousAlgEquiv σ K (toCompletion K (washnitzerAlgebra σ K) (X σ K i)) =
      ⟨_root_.MvPowerSeries.X i, isRestricted_X _ i⟩ := by
  simp

end washnitzerAlgebra

end PresentationComparison

section SupSeminorm

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
  [CommRing B] [Algebra K B] [IsDaggerAlgebra K B]

/-- **The completion map preserves the supremum seminorm**, since contraction along `toCompletion`
is a bijection of classical points preserving residue fields. -/
@[simp]
theorem supSeminorm_toCompletion (a : A) :
    supSeminorm K (toCompletion K A a) = supSeminorm K a := by
  rw [supSeminorm_eq_iSup, supSeminorm_eq_iSup]
  simp_rw [← (isAffinoidAlgebra_completion (K := K) (A := A)).pointNorm_maximalSpectrumComap
    (toCompletion K A)]
  exact (maximalSpectrumComap_toCompletion_bijective (K := K) (A := A)).surjective.iSup_comp
    (pointNorm K · a)

namespace IsDaggerAlgebra

/-- **Morphisms of dagger algebras contract the supremum seminorm**: `|φ a|sup ≤ |a|sup`. -/
theorem supSeminorm_map_le (φ : A →ₐ[K] B) (a : A) :
    supSeminorm K (φ a) ≤ supSeminorm K a := by
  rw [← supSeminorm_toCompletion (K := K) (A := B), ← completionMap_toCompletion,
    ← supSeminorm_toCompletion (K := K) (A := A)]
  exact (isAffinoidAlgebra_completion (K := K) (A := A)).supSeminorm_map_le
    (isAffinoidAlgebra_completion (K := K) (A := B)) (completionMap φ) _

/-- Algebra isomorphisms of dagger algebras preserve the supremum seminorm. -/
@[simp]
theorem supSeminorm_algEquiv (e : A ≃ₐ[K] B) (a : A) :
    supSeminorm K (e a) = supSeminorm K a :=
  le_antisymm (supSeminorm_map_le e.toAlgHom a)
    (by simpa using supSeminorm_map_le e.symm.toAlgHom (e a))

/-- **The kernel of the supremum seminorm on a dagger algebra is the nilradical**: `|a|sup = 0`
if and only if `a` is nilpotent, since `toCompletion` is injective and preserves `supSeminorm`. -/
theorem supSeminorm_eq_zero_iff {a : A} : supSeminorm K a = 0 ↔ IsNilpotent a := by
  rw [← supSeminorm_toCompletion (K := K) (A := A),
    (isAffinoidAlgebra_completion (K := K) (A := A)).supSeminorm_eq_zero_iff]
  exact ⟨fun ⟨n, hn⟩ ↦ ⟨n, toCompletion_injective (K := K) (A := A)
    (by rw [map_pow, hn, map_zero])⟩, fun ha ↦ ha.map (toCompletion K A)⟩

/-- **The supremum seminorm is a norm precisely on reduced dagger algebras**, in every
characteristic. -/
theorem isReduced_iff_supSeminorm_eq_zero :
    IsReduced A ↔ ∀ a : A, supSeminorm K a = 0 → a = 0 := by
  simp_rw [supSeminorm_eq_zero_iff, isReduced_iff]

end IsDaggerAlgebra

end SupSeminorm

end TauCeti.Dagger
