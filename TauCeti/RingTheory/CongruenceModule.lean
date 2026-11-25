/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Congruence modules of augmented algebras

Let `O` be a commutative ring, `A` a commutative `O`-algebra and `φ : A →ₐ[O] O` an augmentation
with kernel `𝔭`. For an `A`-module `M` (compatibly an `O`-module) the *congruence module* is the
cokernel
`Ψ_φ(M) = coker (M[𝔭] → (M ⧸ 𝔭 M)_tf)`
of the map from the `𝔭`-torsion submodule `M[𝔭]` to the quotient of `M ⧸ 𝔭 M` by its
`O`-torsion. The *congruence ideal* is `η_φ = φ (Ann_A 𝔭)`. These are the congruence module and
congruence ideal of Iyengar–Khare–Manning in codimension zero. In the intended application `O` is
a discrete valuation ring, `A` a local Hecke algebra, `M` a Hecke module and `φ` the
eigencharacter of an eigenform; Ribet's level-changing arguments compare such modules at two
levels.

## Main definitions

* `AlgHom.congruenceIdeal φ`: the congruence ideal `η_φ = φ (Ann_A (ker φ))` of `O`.
* `AlgHom.congruenceMap φ M`: the canonical map `M[ker φ] → (M ⧸ (ker φ) M)_tf`.
* `AlgHom.congruenceModule φ M`: its cokernel `Ψ_φ(M)`.
* `AlgHom.congruenceModuleMk φ M`: the surjection `M → Ψ_φ(M)`.
* `AlgHom.congruenceModuleMap φ f`: the map `Ψ_φ(M) → Ψ_φ(N)` induced by an `A`-linear map.

## Main results

* `AlgHom.congruenceModuleMk_eq_zero_iff`: `m` vanishes in `Ψ_φ(M)` exactly when
  `s • (m - n) ∈ (ker φ) M` for some `n ∈ M[ker φ]` and some nonzerodivisor `s` of `O`.
* `AlgHom.isTorsion_congruenceModule_iff_surjective`: `Ψ_φ(M)` is torsion exactly when the map
  `M[ker φ] → M ⧸ (ker φ) M` becomes surjective after inverting the nonzerodivisors of `O`.
* `AlgHom.congruenceModuleCongr`, `AlgHom.congruenceModulePiEquiv`: invariance under
  isomorphisms of `A`-modules and compatibility with finite products.
* `AlgHom.congruenceModuleSelfEquiv`: `Ψ_φ(A) ≃ O ⧸ η_φ`.
* `AlgHom.congruenceModuleEquivOfBasis`: `Ψ_φ(M) ≃ (O ⧸ η_φ)ⁿ` for `M` free of rank `n` over `A`.

## References

* S. B. Iyengar, C. B. Khare, J. Manning, *Congruence modules and the Wiles–Lenstra–Diamond
  numerical criterion in higher codimensions*, Invent. Math. (2024),
  <https://doi.org/10.1007/s00222-024-01292-y>, §2.2, Proposition 2.10 and Example 2.11,
  <https://par.nsf.gov/servlets/purl/10585269>.
* K. A. Ribet, *Report on mod ℓ representations of Gal(Q-bar/Q)*, §7, for the level-change
  application.
-/

public section

open Submodule

open scoped nonZeroDivisors

namespace AlgHom

variable {O A : Type*} [CommRing O] [CommRing A] [Algebra O A] (φ : A →ₐ[O] O)

/-- An augmentation `φ : A →ₐ[O] O` is surjective, since `φ (algebraMap O A x) = x`. -/
theorem augmentation_surjective : Function.Surjective φ :=
  Function.LeftInverse.surjective φ.commutes

/-- The *congruence ideal* `η_φ = φ (Ann_A (ker φ))` of an augmentation `φ : A →ₐ[O] O`. -/
def congruenceIdeal : Ideal O :=
  (RingHom.ker φ).annihilator.map φ

/-- An element of `O` lies in the congruence ideal exactly when it is the value of an element of
`A` killed by `ker φ`. -/
theorem mem_congruenceIdeal {x : O} :
    x ∈ φ.congruenceIdeal ↔ ∃ a : A, (∀ b ∈ RingHom.ker φ, b * a = 0) ∧ φ a = x := by
  rw [congruenceIdeal, Ideal.mem_map_iff_of_surjective _ φ.augmentation_surjective]
  simp [Submodule.mem_annihilator, mul_comm]

variable (M : Type*) [AddCommGroup M] [Module A M] [Module O M] [IsScalarTower O A M]

/-- The canonical map `M[ker φ] → (M ⧸ (ker φ) M)_tf` from the `ker φ`-torsion of `M` to the
quotient of `M ⧸ (ker φ) M` by its `O`-torsion. -/
noncomputable def congruenceMap :
    torsionBySet A M (RingHom.ker φ) →ₗ[O]
      (M ⧸ (RingHom.ker φ • ⊤ : Submodule A M)) ⧸
        torsion O (M ⧸ (RingHom.ker φ • ⊤ : Submodule A M)) :=
  (torsion O _).mkQ ∘ₗ (RingHom.ker φ • ⊤ : Submodule A M).mkQ.restrictScalars O ∘ₗ
    (torsionBySet A M (RingHom.ker φ)).subtype.restrictScalars O

/-- The canonical map sends `n` to the class of `n` modulo `(ker φ) M` and torsion. -/
@[simp]
theorem congruenceMap_apply (n : torsionBySet A M (RingHom.ker φ)) :
    φ.congruenceMap M n = Submodule.Quotient.mk (Submodule.Quotient.mk (n : M)) :=
  (rfl)

/-- The *congruence module* `Ψ_φ(M) = coker (M[ker φ] → (M ⧸ (ker φ) M)_tf)`, the existing
quotient by the range of `AlgHom.congruenceMap`. -/
abbrev congruenceModule : Type _ :=
  _ ⧸ LinearMap.range (φ.congruenceMap M)

/-- The projection `M → Ψ_φ(M)`. -/
noncomputable def congruenceModuleMk : M →ₗ[O] φ.congruenceModule M :=
  (LinearMap.range (φ.congruenceMap M)).mkQ ∘ₗ (torsion O _).mkQ ∘ₗ
    (RingHom.ker φ • ⊤ : Submodule A M).mkQ.restrictScalars O

/-- The class of `m` in `Ψ_φ(M)` is its image in the iterated quotient. This is not a simp
lemma, so that simp keeps working with `AlgHom.congruenceModuleMk`. -/
theorem congruenceModuleMk_apply (m : M) :
    φ.congruenceModuleMk M m =
      Submodule.Quotient.mk (Submodule.Quotient.mk (Submodule.Quotient.mk m)) :=
  (rfl)

/-- Every element of `Ψ_φ(M)` is the class of an element of `M`. -/
theorem congruenceModuleMk_surjective : Function.Surjective (φ.congruenceModuleMk M) :=
  (mkQ_surjective _).comp ((mkQ_surjective _).comp (mkQ_surjective _))

/-- Linear maps out of `Ψ_φ(M)` agree when they agree on the image of `M`. -/
@[ext high]
theorem congruenceModule_hom_ext {X : Type*} [AddCommGroup X] [Module O X]
    {f g : φ.congruenceModule M →ₗ[O] X}
    (h : f ∘ₗ φ.congruenceModuleMk M = g ∘ₗ φ.congruenceModuleMk M) : f = g :=
  (LinearMap.cancel_right (φ.congruenceModuleMk_surjective M)).1 h

variable {M} in
/-- An element `m` vanishes in `Ψ_φ(M)` exactly when, for some `n ∈ M[ker φ]` and some
nonzerodivisor `s` of `O`, `s • (m - n)` lies in `(ker φ) M`. -/
theorem congruenceModuleMk_eq_zero_iff (m : M) :
    φ.congruenceModuleMk M m = 0 ↔ ∃ n ∈ torsionBySet A M (RingHom.ker φ), ∃ s ∈ O⁰,
      s • (m - n) ∈ (RingHom.ker φ • ⊤ : Submodule A M) := by
  rw [congruenceModuleMk, LinearMap.comp_apply, mkQ_apply, Submodule.Quotient.mk_eq_zero]
  simp only [LinearMap.mem_range, congruenceMap_apply, LinearMap.comp_apply, mkQ_apply,
    LinearMap.restrictScalars_apply, Submodule.Quotient.eq, mem_torsion_iff, Subtype.exists,
    Submonoid.mk_smul, exists_prop]
  have key (n : M) (s : O) : s • (Submodule.Quotient.mk n - Submodule.Quotient.mk m :
      M ⧸ (RingHom.ker φ • ⊤ : Submodule A M)) = 0 ↔
      s • (m - n) ∈ (RingHom.ker φ • ⊤ : Submodule A M) := by
    rw [← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
      ← neg_mem_iff, ← smul_neg, neg_sub]
  simp only [key]

/-- `Ψ_φ(M)` is finitely generated over `O` when `M` is. -/
instance [Module.Finite O M] : Module.Finite O (φ.congruenceModule M) :=
  Module.Finite.of_surjective _ (φ.congruenceModuleMk_surjective M)

/-- `Ψ_φ(M)` is torsion exactly when every `m : M` has a nonzerodivisor multiple congruent modulo
`(ker φ) M` to an element of `M[ker φ]`. -/
theorem isTorsion_congruenceModule_iff :
    Module.IsTorsion O (φ.congruenceModule M) ↔ ∀ m : M, ∃ s ∈ O⁰,
      ∃ n ∈ torsionBySet A M (RingHom.ker φ), s • m - n ∈ (RingHom.ker φ • ⊤ : Submodule A M) := by
  refine ⟨fun h m => ?_, fun h x => ?_⟩
  · obtain ⟨t, ht⟩ := h (x := φ.congruenceModuleMk M m)
    rw [Submonoid.smul_def, ← map_smul, congruenceModuleMk_eq_zero_iff] at ht
    obtain ⟨n, hn, s, hs, hsn⟩ := ht
    refine ⟨s * t, mul_mem hs t.property, s • n, Submodule.smul_of_tower_mem _ _ hn, ?_⟩
    rwa [mul_smul, ← smul_sub]
  · obtain ⟨m, rfl⟩ := φ.congruenceModuleMk_surjective M x
    obtain ⟨s, hs, n, hn, hsn⟩ := h m
    refine ⟨⟨s, hs⟩, ?_⟩
    rw [Submonoid.smul_def, ← map_smul, congruenceModuleMk_eq_zero_iff]
    exact ⟨n, hn, 1, one_mem _, by rwa [one_smul]⟩

/-- `Ψ_φ(M)` is torsion exactly when the map `M[ker φ] → M ⧸ (ker φ) M` becomes surjective after
inverting the nonzerodivisors of `O`. In particular `Ψ_φ(M)` is torsion when this map is an
isomorphism after extending scalars to the total ring of fractions of `O`. -/
theorem isTorsion_congruenceModule_iff_surjective :
    Module.IsTorsion O (φ.congruenceModule M) ↔ Function.Surjective (LocalizedModule.map O⁰
      ((RingHom.ker φ • ⊤ : Submodule A M).mkQ.restrictScalars O ∘ₗ
        (torsionBySet A M (RingHom.ker φ)).subtype.restrictScalars O)) := by
  rw [LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker,
    LocalizedModule.subsingleton_iff, isTorsion_congruenceModule_iff]
  have key (s : O) (m n : M) : (Submodule.Quotient.mk n : M ⧸ (RingHom.ker φ • ⊤ : Submodule A M))
      = s • Submodule.Quotient.mk m ↔ s • m - n ∈ (RingHom.ker φ • ⊤ : Submodule A M) := by
    rw [← Submodule.Quotient.mk_smul, eq_comm, Submodule.Quotient.eq]
  refine ⟨fun h x => ?_, fun h m => ?_⟩
  · obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨s, hs, n, hn, hsn⟩ := h m
    refine ⟨s, hs, ?_⟩
    rw [mkQ_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨⟨n, hn⟩, (key s m n).2 hsn⟩
  · obtain ⟨s, hs, h⟩ := h (Submodule.Quotient.mk (Submodule.Quotient.mk m))
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
    obtain ⟨⟨n, hn⟩, h⟩ := h
    exact ⟨s, hs, n, hn, (key s m n).1 h⟩

section Functoriality

variable {M} {N P : Type*} [AddCommGroup N] [Module A N] [Module O N] [IsScalarTower O A N]
  [AddCommGroup P] [Module A P] [Module O P] [IsScalarTower O A P]

/-- An `A`-linear map sends the kernel of `M → Ψ_φ(M)` into the kernel of `N → Ψ_φ(N)`. -/
theorem ker_congruenceModuleMk_le_comap (f : M →ₗ[A] N) :
    LinearMap.ker (φ.congruenceModuleMk M) ≤
      (LinearMap.ker (φ.congruenceModuleMk N)).comap (f.restrictScalars O) := by
  intro m hm
  rw [LinearMap.mem_ker, congruenceModuleMk_eq_zero_iff] at hm
  obtain ⟨n, hn, s, hs, hsn⟩ := hm
  rw [mem_comap, LinearMap.mem_ker, LinearMap.restrictScalars_apply,
    congruenceModuleMk_eq_zero_iff]
  refine ⟨f n, ?_, s, hs, ?_⟩
  · rw [mem_torsionBySet_iff] at hn ⊢
    intro a
    rw [← map_smul, hn a, map_zero]
  · have h := Submodule.mem_map_of_mem (f := f) hsn
    rw [Submodule.map_smul''] at h
    rw [← map_sub, ← f.map_smul_of_tower]
    exact (smul_mono_right _ le_top : _ • map f ⊤ ≤ _) h

/-- The map `Ψ_φ(M) → Ψ_φ(N)` induced by an `A`-linear map `M → N`. -/
noncomputable def congruenceModuleMap (f : M →ₗ[A] N) :
    φ.congruenceModule M →ₗ[O] φ.congruenceModule N :=
  (LinearMap.ker (φ.congruenceModuleMk M)).liftQ (φ.congruenceModuleMk N ∘ₗ f.restrictScalars O)
      (φ.ker_congruenceModuleMk_le_comap f) ∘ₗ
    ((φ.congruenceModuleMk M).quotKerEquivOfSurjective
      (φ.congruenceModuleMk_surjective M)).symm.toLinearMap

@[simp]
theorem congruenceModuleMap_congruenceModuleMk (f : M →ₗ[A] N) (m : M) :
    φ.congruenceModuleMap f (φ.congruenceModuleMk M m) = φ.congruenceModuleMk N (f m) := by
  have : ((φ.congruenceModuleMk M).quotKerEquivOfSurjective
      (φ.congruenceModuleMk_surjective M)).symm (φ.congruenceModuleMk M m) =
        Submodule.Quotient.mk m := by
    rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
  simp only [congruenceModuleMap, LinearMap.comp_apply, LinearEquiv.coe_coe, this]
  exact liftQ_apply _ _ _

@[simp]
theorem congruenceModuleMap_comp_congruenceModuleMk (f : M →ₗ[A] N) :
    φ.congruenceModuleMap f ∘ₗ φ.congruenceModuleMk M =
      φ.congruenceModuleMk N ∘ₗ f.restrictScalars O :=
  LinearMap.ext fun m => φ.congruenceModuleMap_congruenceModuleMk f m

@[simp]
theorem congruenceModuleMap_id :
    φ.congruenceModuleMap (LinearMap.id : M →ₗ[A] M) = LinearMap.id := by
  ext; simp

theorem congruenceModuleMap_comp (g : N →ₗ[A] P) (f : M →ₗ[A] N) :
    φ.congruenceModuleMap (g ∘ₗ f) = φ.congruenceModuleMap g ∘ₗ φ.congruenceModuleMap f := by
  ext; simp

@[simp]
theorem congruenceModuleMap_congruenceModuleMap (g : N →ₗ[A] P) (f : M →ₗ[A] N)
    (x : φ.congruenceModule M) :
    φ.congruenceModuleMap g (φ.congruenceModuleMap f x) = φ.congruenceModuleMap (g ∘ₗ f) x := by
  rw [congruenceModuleMap_comp, LinearMap.comp_apply]

@[simp]
theorem congruenceModuleMap_zero :
    φ.congruenceModuleMap (0 : M →ₗ[A] N) = 0 := by
  ext; simp

@[simp]
theorem congruenceModuleMap_add (f g : M →ₗ[A] N) :
    φ.congruenceModuleMap (f + g) = φ.congruenceModuleMap f + φ.congruenceModuleMap g := by
  ext; simp

/-- `Ψ_φ` sends isomorphic `A`-modules to isomorphic `O`-modules. -/
noncomputable def congruenceModuleCongr (e : M ≃ₗ[A] N) :
    φ.congruenceModule M ≃ₗ[O] φ.congruenceModule N :=
  LinearEquiv.ofLinearMap (φ.congruenceModuleMap e.toLinearMap)
    (φ.congruenceModuleMap e.symm.toLinearMap) (by ext; simp) (by ext; simp)

@[simp]
theorem congruenceModuleCongr_congruenceModuleMk (e : M ≃ₗ[A] N) (m : M) :
    φ.congruenceModuleCongr e (φ.congruenceModuleMk M m) = φ.congruenceModuleMk N (e m) :=
  φ.congruenceModuleMap_congruenceModuleMk _ m

@[simp]
theorem congruenceModuleCongr_symm (e : M ≃ₗ[A] N) :
    (φ.congruenceModuleCongr e).symm = φ.congruenceModuleCongr e.symm :=
  (rfl)

@[simp]
theorem congruenceModuleCongr_refl :
    φ.congruenceModuleCongr (LinearEquiv.refl A M) = LinearEquiv.refl O _ := by
  ext x
  obtain ⟨m, rfl⟩ := φ.congruenceModuleMk_surjective M x
  simp

@[simp]
theorem congruenceModuleCongr_trans (e₁ : M ≃ₗ[A] N) (e₂ : N ≃ₗ[A] P) :
    φ.congruenceModuleCongr (e₁ ≪≫ₗ e₂) =
      φ.congruenceModuleCongr e₁ ≪≫ₗ φ.congruenceModuleCongr e₂ := by
  ext x
  obtain ⟨m, rfl⟩ := φ.congruenceModuleMk_surjective M x
  simp

end Functoriality

section Pi

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (M : ι → Type*) [∀ i, AddCommGroup (M i)]
  [∀ i, Module A (M i)] [∀ i, Module O (M i)] [∀ i, IsScalarTower O A (M i)]

/-- `Ψ_φ` commutes with finite products. -/
noncomputable def congruenceModulePiEquiv :
    φ.congruenceModule (∀ i, M i) ≃ₗ[O] ∀ i, φ.congruenceModule (M i) :=
  LinearEquiv.ofLinearMap (LinearMap.pi fun i => φ.congruenceModuleMap (LinearMap.proj i))
    (∑ i, φ.congruenceModuleMap (LinearMap.single A M i) ∘ₗ LinearMap.proj i)
    (by
      refine LinearMap.ext fun x => funext fun j => ?_
      rw [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sum_apply, map_sum,
        Finset.sum_eq_single j (fun i _ hij => ?_) (by simp)]
      · simp [LinearMap.proj_comp_single_same]
      · simp [LinearMap.proj_comp_single_ne _ _ _ _ hij.symm])
    (by
      refine φ.congruenceModule_hom_ext _ (LinearMap.ext fun m => ?_)
      simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.proj_apply,
        LinearMap.pi_apply, congruenceModuleMap_congruenceModuleMk, LinearMap.id_apply, ← map_sum]
      congr 1
      exact Finset.univ_sum_single m)

@[simp]
theorem congruenceModulePiEquiv_congruenceModuleMk (m : ∀ i, M i) (i : ι) :
    φ.congruenceModulePiEquiv M (φ.congruenceModuleMk _ m) i = φ.congruenceModuleMk _ (m i) :=
  φ.congruenceModuleMap_congruenceModuleMk _ m

/-- The inverse of `AlgHom.congruenceModulePiEquiv` sends the family of classes of `m i` to the
class of `m`. -/
@[simp]
theorem congruenceModulePiEquiv_symm_congruenceModuleMk (m : ∀ i, M i) :
    (φ.congruenceModulePiEquiv M).symm (fun i => φ.congruenceModuleMk _ (m i)) =
      φ.congruenceModuleMk _ m := by
  rw [LinearEquiv.symm_apply_eq]
  ext i
  simp

end Pi

section Self

/-- An element `a` of `A` vanishes in `Ψ_φ(A)` exactly when `φ a` lies in `η_φ`. -/
theorem congruenceModuleMk_self_eq_zero_iff (a : A) :
    φ.congruenceModuleMk A a = 0 ↔ φ a ∈ φ.congruenceIdeal := by
  rw [congruenceModuleMk_eq_zero_iff, mem_congruenceIdeal]
  simp only [mem_torsionBySet_iff, Subtype.forall, smul_eq_mul, Ideal.mul_top, RingHom.mem_ker]
  constructor
  · rintro ⟨n, hn, s, hs, h⟩
    refine ⟨n, hn, ?_⟩
    rw [map_smul, map_sub, smul_eq_mul] at h
    exact (sub_eq_zero.1 (mem_nonZeroDivisors_iff_right.1 hs _ (by rwa [mul_comm]))).symm
  · rintro ⟨n, hn, h⟩
    exact ⟨n, hn, 1, one_mem _, by rw [one_smul, map_sub, h, sub_self]⟩

/-- The congruence module of `A` itself is `O ⧸ η_φ`: the class of `a` corresponds to the class
of `φ a`. -/
noncomputable def congruenceModuleSelfEquiv : φ.congruenceModule A ≃ₗ[O] O ⧸ φ.congruenceIdeal :=
  ((φ.congruenceModuleMk A).quotKerEquivOfSurjective (φ.congruenceModuleMk_surjective A)).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (by
      ext a
      simp [congruenceModuleMk_self_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]) ≪≫ₗ
    ((φ.congruenceIdeal.mkQ ∘ₗ φ.toLinearMap).quotKerEquivOfSurjective
      ((mkQ_surjective _).comp φ.augmentation_surjective))

@[simp]
theorem congruenceModuleSelfEquiv_congruenceModuleMk (a : A) :
    φ.congruenceModuleSelfEquiv (φ.congruenceModuleMk A a) = Submodule.Quotient.mk (φ a) := by
  simp [congruenceModuleSelfEquiv, LinearEquiv.trans_apply]

@[simp]
theorem congruenceModuleSelfEquiv_symm_mk (x : O) :
    φ.congruenceModuleSelfEquiv.symm (Ideal.Quotient.mk φ.congruenceIdeal x) =
      φ.congruenceModuleMk A (algebraMap O A x) := by
  simp [← Ideal.Quotient.mk_eq_mk, LinearEquiv.symm_apply_eq]

end Self

section Basis

variable {M} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- If `M` is free over `A` with a finite basis indexed by `ι`, then `Ψ_φ(M) ≃ (O ⧸ η_φ)^ι`. -/
noncomputable def congruenceModuleEquivOfBasis (b : Module.Basis ι A M) :
    φ.congruenceModule M ≃ₗ[O] ι → O ⧸ φ.congruenceIdeal :=
  φ.congruenceModuleCongr b.equivFun ≪≫ₗ φ.congruenceModulePiEquiv (fun _ => A) ≪≫ₗ
    LinearEquiv.piCongrRight fun _ => φ.congruenceModuleSelfEquiv

@[simp]
theorem congruenceModuleEquivOfBasis_congruenceModuleMk (b : Module.Basis ι A M) (m : M) (i : ι) :
    φ.congruenceModuleEquivOfBasis b (φ.congruenceModuleMk M m) i =
      Submodule.Quotient.mk (φ (b.repr m i)) := by
  simp [congruenceModuleEquivOfBasis]

/-- The inverse of `AlgHom.congruenceModuleEquivOfBasis` sends the family of classes of `x i` to
the class of `∑ i, x i • b i`. -/
@[simp]
theorem congruenceModuleEquivOfBasis_symm_mk (b : Module.Basis ι A M) (x : ι → O) :
    (φ.congruenceModuleEquivOfBasis b).symm
        (fun i => Ideal.Quotient.mk φ.congruenceIdeal (x i)) =
      φ.congruenceModuleMk M (∑ i, x i • b i) := by
  simp only [← Ideal.Quotient.mk_eq_mk]
  rw [LinearEquiv.symm_apply_eq]
  ext i
  have h : ∑ j, x j • b j = ∑ j, algebraMap O A (x j) • b j := by simp [algebraMap_smul]
  rw [congruenceModuleEquivOfBasis_congruenceModuleMk, h, b.repr_sum_self]
  simp

end Basis

end AlgHom
