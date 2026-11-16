/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import TauCeti.RingTheory.AdicCompletion.Finite
public import TauCeti.RingTheory.Artinian.LocalRing
public import TauCeti.RingTheory.MatlisDuality.Finite
import TauCeti.RingTheory.AdicCompletion.Algebra

/-!
# Matlis duality for Artinian modules and over the completion

Let `R` be a commutative Noetherian local ring with maximal ideal `𝔪`, residue field `κ`, and
`𝔪`-adic completion `R̂`, and let `ι : κ →ₗ[R] E` be an injective envelope of `κ`. This file
completes Matlis duality on the Artinian side and establishes the general duality between Artinian
`R`-modules and finitely generated `R̂`-modules without assuming that `R` is complete or that `κ`
is finite.

Every Artinian module over a commutative local ring has an essential finite-dimensional socle
(`TauCeti.RingTheory.Artinian.LocalRing`), and therefore embeds into a finite power `Fin n → E`
of any injective module containing `κ` (`TauCeti.exists_injective_linearMap_fin_of_isArtinian`).
When `E` is the injective hull of `κ` over a Noetherian local ring, dualizing this embedding
against `End_R(E) ≃ R̂` shows that `Hom_R(M, E)` is a finite `R̂`-module for every Artinian
`R`-module `M`, establishing the converse to
`TauCeti.IsInjectiveEnvelope.isArtinian_of_finite_adicCompletion_linearMap`.

When `R` is complete, `Hom_R(M, E)` is finite over `R`, and applying finite-module biduality to
`Hom_R(M, E)` proves that the cokernel of evaluation `M → Hom_R(Hom_R(M, E), E)` has trivial
Matlis dual and hence vanishes (`TauCeti.IsInjectiveEnvelope.bijective_applyₗ_of_isArtinian`).

Over an arbitrary Noetherian local ring `R`, the canonical `R̂`-module structure on `E` makes `E`
an injective envelope of the residue field of `R̂` (`TauCeti.IsInjectiveEnvelope.adicCompletion`).
Applying complete Matlis duality over `R̂` and the identification of `R`-linear and `R̂`-linear maps
on `𝔪`-power-torsion modules then yields the anti-equivalence between Artinian `R`-modules and
finite `R̂`-modules, and identifies the double Matlis dual `Hom_R(Hom_R(N, E), E)` of any finite
`R`-module `N` with its `𝔪`-adic completion `AdicCompletion 𝔪 N`
(`TauCeti.IsInjectiveEnvelope.adicCompletionEquivBidualOfFinite`).

## Main results

* `TauCeti.exists_injective_linearMap_fin_of_isArtinian`: over any commutative local ring, every
  Artinian module embeds into `Fin n → E` for any injective module `E` containing the residue field.
* `TauCeti.IsInjectiveEnvelope.finite_adicCompletion_linearMap_of_isArtinian` and
  `TauCeti.IsInjectiveEnvelope.isArtinian_iff_finite_adicCompletion_linearMap`: an `R`-module is
  Artinian iff its Matlis dual is finite over `R̂`.
* `TauCeti.IsInjectiveEnvelope.finite_linearMap_of_isArtinian`,
  `TauCeti.IsInjectiveEnvelope.bijective_applyₗ_of_isArtinian`, and
  `TauCeti.IsInjectiveEnvelope.evalEquivOfArtinian`: Artinian Matlis biduality over a complete
  Noetherian local ring.
* `TauCeti.IsInjectiveEnvelope.adicCompletion`: `E`, with its canonical `R̂`-module structure, is
  an injective envelope of the residue field of `R̂`.
* `TauCeti.IsInjectiveEnvelope.isArtinian_adicCompletion_linearMap_of_finite`,
  `TauCeti.IsInjectiveEnvelope.evalEquivAdicCompletionOfArtinian`, and
  `TauCeti.IsInjectiveEnvelope.evalEquivOfFiniteAdicCompletion`: Matlis duality between Artinian
  `R`-modules and finite `R̂`-modules over any Noetherian local ring.
* `TauCeti.IsInjectiveEnvelope.adicCompletionEquivBidualOfFinite`: for any finite `R`-module `N`,
  `AdicCompletion 𝔪 N ≃ₗ[R̂] Hom_R(Hom_R(N, E), E)`, intertwining `AdicCompletion.of` with
  evaluation.

## References

* The Stacks Project, Proposition 47.7.8 and Remark 47.7.9, Tags 08Z9 and 0EGL.
* W. Bruns, J. Herzog, *Cohen–Macaulay rings*, Theorem 3.2.13.
-/

public section

noncomputable section

namespace TauCeti

open IsLocalRing LinearMap

universe u v w z

section Embedding

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {E : Type v} [AddCommGroup E] [Module R E] [Small.{v} R]
  {ι : ResidueField R →ₗ[R] E}

/-- Every Artinian module over a commutative local ring embeds into a finite power `Fin n → E` of
any injective module containing the residue field. Neither a Noetherian hypothesis nor essentiality
of `ι` is required. -/
theorem exists_injective_linearMap_fin_of_isArtinian [Module.Injective R E]
    (hι : Function.Injective ι) (M : Type w) [AddCommGroup M] [Module R M] [IsArtinian R M] :
    ∃ (n : ℕ) (f : M →ₗ[R] (Fin n → E)), Function.Injective f := by
  obtain ⟨n, ⟨e⟩⟩ := exists_linearEquiv_fin_residueField_torsionBySet (R := R) (M := M)
  let S := Submodule.torsionBySet R M (maximalIdeal R : Set R)
  -- Map the socle `M[𝔪] ≃ κⁿ` coordinatewise into `Eⁿ`.
  let g : S →ₗ[R] (Fin n → E) := (LinearMap.pi fun i ↦ ι.comp (LinearMap.proj i)).comp e.toLinearMap
  have hg : Function.Injective g := by
    refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ e.injective <| funext fun i ↦ hι ?_
    simpa [g] using congrFun hx i
  -- Extend from the essential socle to all of `M` by injectivity of `Fin n → E`.
  obtain ⟨f, hf⟩ := Module.Injective.extension_property R (Fin n → E) S M S.subtype
    S.injective_subtype g
  refine ⟨n, f, ?_⟩
  have hrange : IsEssential (LinearMap.range S.subtype) := by
    rw [Submodule.range_subtype]
    exact isEssential_torsionBySet_maximalIdeal
  exact hrange.injective_of_injective_comp (hf.symm ▸ hg)

end Embedding

namespace IsInjectiveEnvelope

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  {E : Type v} [AddCommGroup E] [Module R E]
  {ι : ResidueField R →ₗ[R] E} (hι : IsInjectiveEnvelope ι)

include hι

section ArtinianDual

variable [Small.{v} R]

/-- The `R`-algebra isomorphism `R̂ ≃ End_R(E)` upgraded to an `R̂`-linear equivalence for the
canonical completion action on `E`. -/
def adicCompletionEquivEndLinear :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    _root_.AdicCompletion (maximalIdeal R) R ≃ₗ[_root_.AdicCompletion (maximalIdeal R) R]
      Module.End R E := by
  letI := AdicCompletion.torsionModule hι.mem_primaryComponent
  exact
    { toFun := hι.adicCompletionEquivEnd
      invFun := hι.adicCompletionEquivEnd.symm
      left_inv := hι.adicCompletionEquivEnd.left_inv
      right_inv := hι.adicCompletionEquivEnd.right_inv
      map_add' := map_add hι.adicCompletionEquivEnd
      map_smul' := fun a b ↦ LinearMap.ext fun x ↦ by
        simp only [smul_eq_mul, RingHom.id_apply, LinearMap.smul_apply]
        rw [hι.adicCompletionEquivEnd_apply hι.mem_primaryComponent,
          hι.adicCompletionEquivEnd_apply hι.mem_primaryComponent, mul_smul] }

@[simp]
theorem adicCompletionEquivEndLinear_apply (a : _root_.AdicCompletion (maximalIdeal R) R) :
    hι.adicCompletionEquivEndLinear a = hι.adicCompletionEquivEnd a := (rfl)

@[simp]
theorem adicCompletionEquivEndLinear_symm_apply (f : Module.End R E) :
    hι.adicCompletionEquivEndLinear.symm f = hι.adicCompletionEquivEnd.symm f := (rfl)

/-- The Matlis dual of an Artinian module over a Noetherian local ring is finitely generated over
the completion `R̂`. Completeness of `R` is not needed. -/
theorem finite_adicCompletion_linearMap_of_isArtinian (M : Type w) [AddCommGroup M] [Module R M]
    [IsArtinian R M] :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) (M →ₗ[R] E) := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := hι.moduleInjective
  obtain ⟨n, f, hf⟩ := exists_injective_linearMap_fin_of_isArtinian hι.injective M
  -- Precomposition with `f : M ↪ Eⁿ` surjects `Hom_R(Eⁿ, E) ≃ End_R(E)ⁿ ≃ R̂ⁿ` onto `Hom_R(M, E)`.
  have hsurj : Function.Surjective (f.lcomp (_root_.AdicCompletion (maximalIdeal R) R) E) :=
    fun g ↦ Module.Injective.extension_property R E M (Fin n → E) f hf g
  let e : (Fin n → _root_.AdicCompletion (maximalIdeal R) R) ≃ₗ[_root_.AdicCompletion
      (maximalIdeal R) R] ((Fin n → E) →ₗ[R] E) :=
    (LinearEquiv.piCongrRight fun _ ↦ hι.adicCompletionEquivEndLinear).trans
      (LinearMap.lsum R (fun _ : Fin n ↦ E) (_root_.AdicCompletion (maximalIdeal R) R))
  exact Module.Finite.of_surjective ((f.lcomp _ E).comp e.toLinearMap)
    (hsurj.comp e.surjective)

/-- Over a Noetherian local ring, a module is Artinian iff its Matlis dual is finitely generated
over the completion `R̂`. -/
theorem isArtinian_iff_finite_adicCompletion_linearMap (M : Type w) [AddCommGroup M] [Module R M] :
    IsArtinian R M ↔
      letI := AdicCompletion.torsionModule hι.mem_primaryComponent
      Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) (M →ₗ[R] E) :=
  ⟨fun _ ↦ hι.finite_adicCompletion_linearMap_of_isArtinian M,
    hι.isArtinian_of_finite_adicCompletion_linearMap⟩

section Complete

variable [IsAdicComplete (maximalIdeal R) R]

/-- The Matlis dual of an Artinian module over a complete Noetherian local ring is finitely
generated over `R`. -/
theorem finite_linearMap_of_isArtinian (M : Type w) [AddCommGroup M] [Module R M]
    [IsArtinian R M] : Module.Finite R (M →ₗ[R] E) := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have : Module.Finite R (_root_.AdicCompletion (maximalIdeal R) R) :=
    Module.Finite.equiv (_root_.AdicCompletion.ofLinearEquiv (maximalIdeal R) R)
  have : Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) (M →ₗ[R] E) :=
    hι.finite_adicCompletion_linearMap_of_isArtinian M
  exact Module.Finite.trans (_root_.AdicCompletion (maximalIdeal R) R) (M →ₗ[R] E)

/-- Over a complete Noetherian local ring, a module is Artinian iff its Matlis dual is finitely
generated over `R`. -/
theorem isArtinian_iff_finite_linearMap (M : Type w) [AddCommGroup M] [Module R M] :
    IsArtinian R M ↔ Module.Finite R (M →ₗ[R] E) := by
  refine ⟨fun _ ↦ hι.finite_linearMap_of_isArtinian M, fun _ ↦ ?_⟩
  have := hι.moduleInjective
  exact isArtinian_of_isNoetherian_linearMap R hι.injective

/-- **Matlis biduality for Artinian modules over a complete Noetherian local ring**: the canonical
evaluation map `M → Hom_R(Hom_R(M, E), E)` is bijective. -/
theorem bijective_applyₗ_of_isArtinian (M : Type w) [AddCommGroup M] [Module R M]
    [IsArtinian R M] :
    Function.Bijective (applyₗ : M →ₗ[R] (M →ₗ[R] E) →ₗ[R] E) := by
  have := hι.moduleInjective
  refine ⟨injective_applyₗ_of_injective hι.injective, fun φ ↦ ?_⟩
  -- It suffices to show that the cokernel `C` of `applyₗ` admits no nonzero map to `E`.
  let K := LinearMap.range (applyₗ : M →ₗ[R] (M →ₗ[R] E) →ₗ[R] E)
  have hzero : ∀ g : (((M →ₗ[R] E) →ₗ[R] E) ⧸ K) →ₗ[R] E, g = 0 := fun g ↦ by
    have : Module.Finite R (M →ₗ[R] E) := hι.finite_linearMap_of_isArtinian M
    obtain ⟨f, hf⟩ := (hι.bijective_applyₗ_of_finite (M →ₗ[R] E)).2 (g.comp K.mkQ)
    have hf0 : f = 0 := LinearMap.ext fun m ↦ by
      have hm := LinearMap.congr_fun hf (applyₗ m)
      have hmem : applyₗ m ∈ K := ⟨m, rfl⟩
      simpa only [applyₗ_apply_apply, comp_apply, Submodule.mkQ_apply, LinearMap.zero_apply,
        (Submodule.Quotient.mk_eq_zero K).mpr hmem, map_zero] using hm
    refine LinearMap.ext fun y ↦ ?_
    obtain ⟨ψ, rfl⟩ := K.mkQ_surjective y
    have hψ := LinearMap.congr_fun hf ψ
    simpa [hf0] using hψ.symm
  have hq : K.mkQ φ = 0 :=
    (injective_iff_map_eq_zero _).mp (injective_applyₗ_of_injective hι.injective) (K.mkQ φ)
      (LinearMap.ext fun g ↦ by simp [hzero g])
  exact (Submodule.Quotient.mk_eq_zero K).mp hq

/-- Evaluation identifies an Artinian module over a complete Noetherian local ring with its double
Matlis dual. -/
def evalEquivOfArtinian (M : Type w) [AddCommGroup M] [Module R M] [IsArtinian R M] :
    M ≃ₗ[R] ((M →ₗ[R] E) →ₗ[R] E) :=
  LinearEquiv.ofBijective applyₗ (hι.bijective_applyₗ_of_isArtinian M)

@[simp]
theorem evalEquivOfArtinian_apply_apply (M : Type w) [AddCommGroup M] [Module R M] [IsArtinian R M]
    (m : M) (f : M →ₗ[R] E) :
    hι.evalEquivOfArtinian M m f = f m := (rfl)

@[simp]
theorem evalEquivOfArtinian_symm_apply_apply (M : Type w) [AddCommGroup M] [Module R M]
    [IsArtinian R M] (φ : (M →ₗ[R] E) →ₗ[R] E) (f : M →ₗ[R] E) :
    f ((hι.evalEquivOfArtinian M).symm φ) = φ f := by
  simpa only [evalEquivOfArtinian_apply_apply] using
    congrArg (fun ψ : (M →ₗ[R] E) →ₗ[R] E ↦ ψ f) ((hι.evalEquivOfArtinian M).apply_symm_apply φ)

/-- Over a complete Noetherian local ring, Matlis duality is bijective on morphisms into any
finitely generated module. -/
theorem bijective_lcomp_of_finite (M : Type w) [AddCommGroup M] [Module R M]
    (N : Type z) [AddCommGroup N] [Module R N] [Module.Finite R N] :
    Function.Bijective (fun f : M →ₗ[R] N ↦ f.lcomp R E) :=
  bijective_lcomp_of_bijective_applyₗ (hι.bijective_applyₗ_of_finite N)

/-- Over a complete Noetherian local ring, Matlis duality is bijective on morphisms into any
Artinian module. -/
theorem bijective_lcomp_of_isArtinian (M : Type w) [AddCommGroup M] [Module R M]
    (N : Type z) [AddCommGroup N] [Module R N] [IsArtinian R N] :
    Function.Bijective (fun f : M →ₗ[R] N ↦ f.lcomp R E) :=
  bijective_lcomp_of_bijective_applyₗ (hι.bijective_applyₗ_of_isArtinian N)

end Complete

end ArtinianDual

/-! ### The injective hull over the completion -/

/-- The embedding of the residue field of `R̂` into `E`, induced by `ι : κ →ₗ[R] E` via the
bijection `ResidueField R ≃+* ResidueField R̂`. -/
def adicCompletionResidueMap :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    ResidueField (_root_.AdicCompletion (maximalIdeal R) R) →ₗ[_root_.AdicCompletion
      (maximalIdeal R) R] E := by
  letI := AdicCompletion.torsionModule hι.mem_primaryComponent
  let e : ResidueField R ≃+* ResidueField (_root_.AdicCompletion (maximalIdeal R) R) :=
    RingEquiv.ofBijective _ (_root_.AdicCompletion.residueField_map_bijective R)
  refine
    { toFun := fun x ↦ ι (e.symm x)
      map_add' := fun x y ↦ by rw [map_add, map_add]
      map_smul' := fun a x ↦ ?_ }
  dsimp only [RingHom.id_apply]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective
    (_root_.AdicCompletion.evalₐ (maximalIdeal R) 1 a)
  -- `a` and `algebraMap r` have the same residue in `ResidueField R̂`.
  have hres : residue (_root_.AdicCompletion (maximalIdeal R) R) a = e (residue R r) := by
    have hker : RingHom.ker (_root_.AdicCompletion.evalₐ (maximalIdeal R) 1) =
        (maximalIdeal R).map (algebraMap R (_root_.AdicCompletion (maximalIdeal R) R)) := by
      simpa only [pow_one] using
        _root_.AdicCompletion.ker_evalₐ_eq_map_pow (I := maximalIdeal R) (n := 1)
          (IsNoetherian.noetherian _)
    have hdiff : a - algebraMap R (_root_.AdicCompletion (maximalIdeal R) R) r ∈
        maximalIdeal (_root_.AdicCompletion (maximalIdeal R) R) := by
      rw [_root_.AdicCompletion.maximalIdeal_eq_map, ← hker, RingHom.mem_ker, map_sub, ← hr,
        _root_.AdicCompletion.algebraMap_apply, _root_.AdicCompletion.evalₐ_of]
      simp
    have heq : residue (_root_.AdicCompletion (maximalIdeal R) R) a =
        residue (_root_.AdicCompletion (maximalIdeal R) R)
          (algebraMap R (_root_.AdicCompletion (maximalIdeal R) R) r) :=
      sub_eq_zero.mp (by rw [← map_sub]; exact (residue_eq_zero_iff _).mpr hdiff)
    rw [heq]
    exact (ResidueField.map_residue _ r).symm
  -- `ι (e.symm x)` is killed by `𝔪`, so `a` acts on it as `r`.
  have hkill : ι (e.symm x) ∈ Submodule.torsionBySet R E ↑(maximalIdeal R ^ 1) := by
    rw [pow_one, Submodule.mem_torsionBySet_iff]
    rintro ⟨s, hs⟩
    dsimp only
    rw [← map_smul, Algebra.smul_def, ResidueField.algebraMap_eq,
      (residue_eq_zero_iff s).mpr hs, zero_mul, map_zero]
  have hsmul : e.symm (a • x) = r • e.symm x := by
    rw [Algebra.smul_def, ResidueField.algebraMap_eq, hres, map_mul, e.symm_apply_apply,
      Algebra.smul_def, ResidueField.algebraMap_eq]
  rw [hsmul, map_smul, a.torsion_smul_eq hι.mem_primaryComponent (ι (e.symm x)) r hkill hr.symm]

@[simp]
theorem adicCompletionResidueMap_apply_map (x : ResidueField R) :
    hι.adicCompletionResidueMap
      (ResidueField.map (algebraMap R (_root_.AdicCompletion (maximalIdeal R) R)) x) = ι x := by
  let e : ResidueField R ≃+* ResidueField (_root_.AdicCompletion (maximalIdeal R) R) :=
    RingEquiv.ofBijective _ (_root_.AdicCompletion.residueField_map_bijective R)
  exact congrArg ι (e.symm_apply_apply x)

@[simp]
theorem adicCompletionResidueMap_residue_algebraMap (r : R) :
    hι.adicCompletionResidueMap
      (residue (_root_.AdicCompletion (maximalIdeal R) R)
        (algebraMap R (_root_.AdicCompletion (maximalIdeal R) R) r)) = ι (residue R r) := by
  rw [← ResidueField.map_residue (algebraMap R (_root_.AdicCompletion (maximalIdeal R) R)) r,
    hι.adicCompletionResidueMap_apply_map]

section CompletionDuality

variable [Small.{v} R]

/-- **The injective hull of `κ` over `R` is also an injective hull of the residue field of `R̂`
over `R̂`** (Stacks Remark 47.7.9, Tag 0EGL). -/
theorem adicCompletion :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    IsInjectiveEnvelope hι.adicCompletionResidueMap := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := hι.moduleInjective
  refine
    { moduleInjective := AdicCompletion.moduleInjective_of_primaryComponent
        ((isNoetherianRing_iff_ideal_fg R).mp inferInstance (maximalIdeal R))
        hι.mem_primaryComponent
      injective := fun x y hxy ↦ ?_
      isEssential_range := isEssential_iff.mpr fun K hK ↦ ?_ }
  · let e : ResidueField R ≃+* ResidueField (_root_.AdicCompletion (maximalIdeal R) R) :=
      RingEquiv.ofBijective _ (_root_.AdicCompletion.residueField_map_bijective R)
    exact e.symm.injective (hι.injective hxy)
  · -- Restricting to `R`, `range ι̂` has the same elements as `range ι`, which is essential.
    have hK' : LinearMap.range ι ⊓ K.restrictScalars R = ⊥ := by
      refine (Submodule.eq_bot_iff _).mpr fun y hy ↦ ?_
      obtain ⟨⟨x, rfl⟩, hyK⟩ := hy
      have hmem : ι x ∈ LinearMap.range hι.adicCompletionResidueMap ⊓ K :=
        ⟨⟨ResidueField.map _ x, hι.adicCompletionResidueMap_apply_map x⟩, hyK⟩
      rwa [hK, Submodule.mem_bot] at hmem
    have hbot : K.restrictScalars R = ⊥ := isEssential_iff.mp hι.isEssential_range _ hK'
    exact Submodule.ext fun y ↦ by
      simpa using Submodule.ext_iff.mp hbot y

/-! ### General Matlis duality between Artinian `R`-modules and finite `R̂`-modules -/

/-- The Matlis dual `Hom_{R̂}(N, E)` of any finitely generated `R̂`-module is an Artinian
`R`-module. -/
theorem isArtinian_adicCompletion_linearMap_of_finite (N : Type w) [AddCommGroup N]
    [Module (_root_.AdicCompletion (maximalIdeal R) R) N]
    [Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) N] :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    IsArtinian R (N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := hι.adicCompletion.isArtinian_linearMap_of_finite N
  exact (AdicCompletion.isArtinian_iff_of_primaryComponent
    ((isNoetherianRing_iff_ideal_fg R).mp inferInstance (maximalIdeal R))
    (AdicCompletion.mem_primaryComponent_linearMap_of_finite hι.mem_primaryComponent)).mp
    inferInstance

/-- **General Matlis biduality for Artinian `R`-modules**: over any Noetherian local ring `R`,
evaluation identifies an Artinian `R`-module `M` with `Hom_{R̂}(Hom_R(M, E), E)`. -/
def evalEquivAdicCompletionOfArtinian (M : Type w) [AddCommGroup M] [Module R M]
    [IsArtinian R M] :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    M ≃ₗ[R] ((M →ₗ[R] E) →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) := by
  letI := AdicCompletion.torsionModule hι.mem_primaryComponent
  have hfg : (maximalIdeal R).FG :=
    (isNoetherianRing_iff_ideal_fg R).mp inferInstance (maximalIdeal R)
  letI := AdicCompletion.torsionModule
    (mem_primaryComponent_maximalIdeal_of_isArtinian (R := R) (M := M) hfg)
  haveI : IsArtinian (_root_.AdicCompletion (maximalIdeal R) R) M :=
    (AdicCompletion.isArtinian_iff_of_primaryComponent hfg
      (mem_primaryComponent_maximalIdeal_of_isArtinian (R := R) (M := M) hfg)).mpr inferInstance
  let eHom : (M →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) ≃ₗ[_root_.AdicCompletion
      (maximalIdeal R) R] (M →ₗ[R] E) :=
    AdicCompletion.restrictScalarsEquivOfPrimaryComponent hfg
      (mem_primaryComponent_maximalIdeal_of_isArtinian (R := R) (M := M) hfg)
  exact ((hι.adicCompletion.evalEquivOfArtinian M).trans
    (eHom.arrowCongr (LinearEquiv.refl _ E))).restrictScalars R

@[simp]
theorem evalEquivAdicCompletionOfArtinian_apply_apply (M : Type w) [AddCommGroup M] [Module R M]
    [IsArtinian R M] (m : M) (f : M →ₗ[R] E) :
    hι.evalEquivAdicCompletionOfArtinian M m f = f m := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  let := AdicCompletion.torsionModule
    (mem_primaryComponent_maximalIdeal_of_isArtinian (R := R) (M := M)
      ((isNoetherianRing_iff_ideal_fg R).mp inferInstance (maximalIdeal R)))
  simp [evalEquivAdicCompletionOfArtinian]

@[simp]
theorem evalEquivAdicCompletionOfArtinian_symm_apply_apply (M : Type w) [AddCommGroup M]
    [Module R M] [IsArtinian R M]
    (φ : letI := AdicCompletion.torsionModule hι.mem_primaryComponent
      (M →ₗ[R] E) →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) (f : M →ₗ[R] E) :
    f ((hι.evalEquivAdicCompletionOfArtinian M).symm φ) = φ f := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  simpa only [evalEquivAdicCompletionOfArtinian_apply_apply] using
    congrArg (fun ψ : (M →ₗ[R] E) →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E ↦ ψ f)
      ((hι.evalEquivAdicCompletionOfArtinian M).apply_symm_apply φ)

/-- **General Matlis biduality for finite `R̂`-modules**: over any Noetherian local ring `R`,
evaluation identifies a finitely generated `R̂`-module `N` with `Hom_R(Hom_{R̂}(N, E), E)`. -/
def evalEquivOfFiniteAdicCompletion (N : Type w) [AddCommGroup N]
    [Module (_root_.AdicCompletion (maximalIdeal R) R) N]
    [Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) N] :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    N ≃ₗ[_root_.AdicCompletion (maximalIdeal R) R]
      ((N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) →ₗ[R] E) := by
  letI := AdicCompletion.torsionModule hι.mem_primaryComponent
  exact (hι.adicCompletion.evalEquivOfFinite N).trans
    (AdicCompletion.restrictScalarsEquivOfPrimaryComponent
      ((isNoetherianRing_iff_ideal_fg R).mp inferInstance (maximalIdeal R))
      (AdicCompletion.mem_primaryComponent_linearMap_of_finite hι.mem_primaryComponent))

@[simp]
theorem evalEquivOfFiniteAdicCompletion_apply_apply (N : Type w) [AddCommGroup N]
    [Module (_root_.AdicCompletion (maximalIdeal R) R) N]
    [Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) N] (x : N)
    (f : letI := AdicCompletion.torsionModule hι.mem_primaryComponent
      N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) :
    hι.evalEquivOfFiniteAdicCompletion N x f = f x := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  simp [evalEquivOfFiniteAdicCompletion]

@[simp]
theorem evalEquivOfFiniteAdicCompletion_symm_apply_apply (N : Type w) [AddCommGroup N]
    [Module (_root_.AdicCompletion (maximalIdeal R) R) N]
    [Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) N]
    (φ : letI := AdicCompletion.torsionModule hι.mem_primaryComponent
      (N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) →ₗ[R] E)
    (f : letI := AdicCompletion.torsionModule hι.mem_primaryComponent
      N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) :
    f ((hι.evalEquivOfFiniteAdicCompletion N).symm φ) = φ f := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  simpa only [evalEquivOfFiniteAdicCompletion_apply_apply] using
    congrArg (fun ψ : (N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) →ₗ[R] E ↦ ψ f)
      ((hι.evalEquivOfFiniteAdicCompletion N).apply_symm_apply φ)

/-- Over any Noetherian local ring, `Hom_R(-, E)` is bijective on morphisms into an Artinian
`R`-module, valued in `R̂`-linear maps between Matlis duals. -/
theorem bijective_lcomp_adicCompletion_of_isArtinian (M : Type w) [AddCommGroup M] [Module R M]
    (N : Type z) [AddCommGroup N] [Module R N] [IsArtinian R N] :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    Function.Bijective (fun f : M →ₗ[R] N ↦
      f.lcomp (_root_.AdicCompletion (maximalIdeal R) R) E) := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  exact bijective_lcomp_of_evalEquiv (_root_.AdicCompletion (maximalIdeal R) R)
    (hι.evalEquivAdicCompletionOfArtinian N) (hι.evalEquivAdicCompletionOfArtinian_apply_apply N)

/-- Over any Noetherian local ring, `Hom_{R̂}(-, E)` is bijective on morphisms into a finite
`R̂`-module, valued in `R`-linear maps between Matlis duals. -/
theorem bijective_lcomp_of_finite_adicCompletion (M : Type w) [AddCommGroup M]
    [Module (_root_.AdicCompletion (maximalIdeal R) R) M]
    (N : Type z) [AddCommGroup N] [Module (_root_.AdicCompletion (maximalIdeal R) R) N]
    [Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) N] :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    Function.Bijective (fun f : M →ₗ[_root_.AdicCompletion (maximalIdeal R) R] N ↦
      f.lcomp R E) := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  exact bijective_lcomp_of_evalEquiv R
    (hι.evalEquivOfFiniteAdicCompletion N) (hι.evalEquivOfFiniteAdicCompletion_apply_apply N)

/-! ### Double Matlis dual of a finite module as its completion -/

/-- **The double Matlis dual of a finite module is its `𝔪`-adic completion.** For any finitely
generated module `N` over a Noetherian local ring `R`, there is a canonical `R̂`-linear isomorphism
`AdicCompletion 𝔪 N ≃ₗ[R̂] Hom_R(Hom_R(N, E), E)` intertwining `AdicCompletion.of` with evaluation
(`adicCompletionEquivBidualOfFinite_of`). -/
def adicCompletionEquivBidualOfFinite (N : Type w) [AddCommGroup N] [Module R N]
    [Module.Finite R N] :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    _root_.AdicCompletion (maximalIdeal R) N ≃ₗ[_root_.AdicCompletion (maximalIdeal R) R]
      ((N →ₗ[R] E) →ₗ[R] E) := by
  letI := AdicCompletion.torsionModule hι.mem_primaryComponent
  let eLift := (AdicCompletion.torsionLiftEquiv (I := maximalIdeal R) (N := N)
    hι.mem_primaryComponent).restrictScalars R
  let eDual : ((_root_.AdicCompletion (maximalIdeal R) N →ₗ[_root_.AdicCompletion
      (maximalIdeal R) R] E) →ₗ[R] E) ≃ₗ[_root_.AdicCompletion (maximalIdeal R) R]
      ((N →ₗ[R] E) →ₗ[R] E) :=
    { toFun := eLift.toLinearMap.lcomp (_root_.AdicCompletion (maximalIdeal R) R) E
      map_add' := map_add _
      map_smul' := map_smul _
      invFun := eLift.symm.toLinearMap.lcomp (_root_.AdicCompletion (maximalIdeal R) R) E
      left_inv := fun φ ↦ LinearMap.ext fun g ↦ by simp [eLift]
      right_inv := fun φ ↦ LinearMap.ext fun f ↦ by simp [eLift] }
  exact (hι.evalEquivOfFiniteAdicCompletion (_root_.AdicCompletion (maximalIdeal R) N)).trans eDual

/-- Evaluation of `adicCompletionEquivBidualOfFinite` applies the canonical lift of `f` to the
completed element. -/
@[simp]
theorem adicCompletionEquivBidualOfFinite_apply_apply (N : Type w) [AddCommGroup N] [Module R N]
    [Module.Finite R N] (y : _root_.AdicCompletion (maximalIdeal R) N) (f : N →ₗ[R] E) :
    hι.adicCompletionEquivBidualOfFinite N y f =
      AdicCompletion.torsionLiftEquiv hι.mem_primaryComponent f y := by
  simp [adicCompletionEquivBidualOfFinite]

/-- On the image of `N` in `AdicCompletion 𝔪 N`, `adicCompletionEquivBidualOfFinite` agrees with
the Matlis evaluation map `LinearMap.applyₗ`. -/
theorem adicCompletionEquivBidualOfFinite_of (N : Type w) [AddCommGroup N] [Module R N]
    [Module.Finite R N] (x : N) (f : N →ₗ[R] E) :
    hι.adicCompletionEquivBidualOfFinite N (_root_.AdicCompletion.of (maximalIdeal R) N x) f =
      f x := by
  simp

@[simp]
theorem adicCompletionEquivBidualOfFinite_symm_apply_apply (N : Type w) [AddCommGroup N]
    [Module R N] [Module.Finite R N] (φ : (N →ₗ[R] E) →ₗ[R] E) (f : N →ₗ[R] E) :
    AdicCompletion.torsionLiftEquiv hι.mem_primaryComponent f
        ((hι.adicCompletionEquivBidualOfFinite N).symm φ) =
      φ f := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  simpa only [adicCompletionEquivBidualOfFinite_apply_apply] using
    congrArg (fun ψ : (N →ₗ[R] E) →ₗ[R] E ↦ ψ f)
      ((hι.adicCompletionEquivBidualOfFinite N).apply_symm_apply φ)

end CompletionDuality

end IsInjectiveEnvelope

end TauCeti
