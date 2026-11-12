/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Ideal.Operations
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Isomorphisms
import TauCeti.RingTheory.Ideal.Operations

/-!
# Hom spaces out of a projective module

Let `k` be a field and `A` a `k`-algebra. For a projective `A`-module `P` the functor
`Hom_A(P, -)` is exact, so when `Hom_A(P, M)` is finite-dimensional over `k` its dimension
is the sum of the dimensions of the hom spaces into a submodule of `M` and its quotient.

Exactness of `Hom_A(P, -)` also computes the maps from `P` into a reduction `V ⧸ x • V`, for `A`
an algebra over a commutative ring `R` and any `x : R`: they are the reductions modulo `x` of
the maps `P → V`. Over `R = ℤ_p` and `x = p`, this makes the number of maps from a projective
`ℤ_p[G]`-lattice into the reduction of another lattice a function of the
`ℤ_p`-module of maps between the lattices.

## Main results

* `TauCeti.finrank_linearMap_quotient_add_finrank_linearMap`: additivity of `dim_k Hom_A(P, -)`
  for a projective `P`.
* `TauCeti.compRight_mkQ_surjective`: every map from a projective `P` into `V ⧸ N` lifts to `V`.
* `TauCeti.ker_compRight_mkQ_eq_smul_top`: a map `P → V` vanishes modulo a non-zero-divisor `x`
  exactly when it is `x` times a map.
* `TauCeti.ker_compRight_mkQ_eq_smul_top_of_projective`: the same kernel computation for
  a projective `P` and any scalar `x`.
* `TauCeti.quotientSMulTopLinearMapEquiv`: `Hom_A(P, V) ⧸ x • Hom_A(P, V) ≃ Hom_A(P, V ⧸ x • V)`
  for a projective `P` and any scalar `x`.
-/

public section

namespace TauCeti

section Quotient

variable {R A P V : Type*} [CommSemiring R] [Ring A] [Algebra R A] [AddCommGroup P]
  [Module A P] [AddCommGroup V] [Module R V] [Module A V] [IsScalarTower R A V]

variable (R P) [Module.Projective A P] in
/-- **Maps from a projective module into a quotient lift.** For `P` projective, every map
`P → V ⧸ N` is the reduction of a map `P → V`. -/
theorem compRight_mkQ_surjective (N : Submodule A V) :
    Function.Surjective (LinearMap.compRight (M := P) R N.mkQ) := fun g ↦
  Module.projective_lifting_property N.mkQ g N.mkQ_surjective

end Quotient

variable {k A P M : Type*} [Field k] [Ring A] [Algebra k A]
  [AddCommGroup P] [Module A P] [Module.Projective A P]
  [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  [FiniteDimensional k (P →ₗ[A] M)]

variable (k P) in
/-- **`dim_k Hom_A(P, -)` is additive**, for `P` projective and `Hom_A(P, M)` finite-dimensional
over `k`: a submodule and its quotient split the dimension of the hom space out of `P`. Neither
`P` nor `M` needs to be finite-dimensional over `k`. -/
theorem finrank_linearMap_quotient_add_finrank_linearMap (N : Submodule A M) :
    Module.finrank k (P →ₗ[A] M ⧸ N) + Module.finrank k (P →ₗ[A] N)
      = Module.finrank k (P →ₗ[A] M) := by
  set α : (P →ₗ[A] N) →ₗ[k] (P →ₗ[A] M) := LinearMap.compRight k N.subtype with hα
  set β : (P →ₗ[A] M) →ₗ[k] (P →ₗ[A] M ⧸ N) := LinearMap.compRight k N.mkQ with hβ
  have hβsurj : Function.Surjective β := compRight_mkQ_surjective k P N
  have hαinj : Function.Injective α := N.injective_subtype.injective_linearMapComp_left
  have hker : LinearMap.ker β = LinearMap.range α := by
    ext g
    refine ⟨fun hg => ?_, ?_⟩
    · have hmem : ∀ p, g p ∈ N := fun p =>
        (Submodule.Quotient.mk_eq_zero N).mp (DFunLike.congr_fun hg p)
      exact ⟨g.codRestrict N hmem, by ext p; simp [hα]⟩
    · rintro ⟨g', rfl⟩
      ext p
      simp [hα, hβ]
  have h1 := LinearMap.finrank_range_add_finrank_ker β
  rw [hker, LinearMap.range_eq_top.mpr hβsurj, Submodule.topEquiv.finrank_eq,
    ← (LinearEquiv.ofInjective α hαinj).finrank_eq] at h1
  exact h1

section Reduction

open Pointwise

variable {R A P V : Type*} [Ring A] [AddCommGroup P] [Module A P]
  [AddCommGroup V] [Module A V] {x : R}

section CommSemiring

variable [CommSemiring R] [Algebra R A] [Module R V] [IsScalarTower R A V]

variable (P) in
/-- **Maps into `x • V` are multiples of `x`.** For `x : R` a non-zero-divisor on the `A`-module
`V`, a map `P → V` reduces to zero in `V ⧸ x • V` exactly when it is `x` times a map `P → V`. -/
theorem ker_compRight_mkQ_eq_smul_top (hx : IsSMulRegular V x) :
    LinearMap.ker (LinearMap.compRight (M := P) R
      (Ideal.span {algebraMap R A x} • (⊤ : Submodule A V)).mkQ) = x • ⊤ := by
  ext h
  simp only [LinearMap.mem_ker, Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top,
    true_and]
  constructor
  · -- A map into `x • V` is `x` times a map, because multiplication by `x` is injective on `V`.
    intro h0
    have hp (p : P) : ∃ w, x • w = h p := by
      simpa only [Submodule.mem_top, true_and] using
        (Submodule.mem_span_algebraMap_smul_iff (⊤ : Submodule A V) x).mp
          ((Submodule.Quotient.mk_eq_zero _).mp (LinearMap.congr_fun h0 p))
    choose w hw using hp
    refine ⟨{ toFun := w, map_add' := fun p p' ↦ hx ?_, map_smul' := fun a p ↦ hx ?_ }, ?_⟩
    · simp only [smul_add, hw, map_add]
    · simp only [RingHom.id_apply, hw, map_smul, smul_comm x a]
    · ext p
      exact hw p
  · rintro ⟨g, rfl⟩
    ext p
    simp only [LinearMap.compRight_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      Submodule.mkQ_apply, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
    exact (Submodule.mem_span_algebraMap_smul_iff ⊤ x).mpr ⟨g p, Submodule.mem_top, rfl⟩

variable (P) [Module.Projective A P] in
/-- For `P` projective, a map `P → V` vanishes modulo `x` exactly when it is `x` times a map,
without any regularity assumption on `x`. -/
@[simp]
theorem ker_compRight_mkQ_eq_smul_top_of_projective :
    LinearMap.ker (LinearMap.compRight (M := P) R
      (Ideal.span {algebraMap R A x} • (⊤ : Submodule A V)).mkQ) = x • ⊤ := by
  let N : Submodule A V := Ideal.span {algebraMap R A x} • ⊤
  let sx : V →ₗ[A] N := (DistribSMul.toLinearMap A V x).codRestrict N fun v =>
    (Submodule.mem_span_algebraMap_smul_iff ⊤ x).mpr ⟨v, Submodule.mem_top, rfl⟩
  have hsx : Function.Surjective sx := by
    intro v
    obtain ⟨w, _, hw⟩ := (Submodule.mem_span_algebraMap_smul_iff ⊤ x).mp v.property
    refine ⟨w, Subtype.ext ?_⟩
    simpa only [sx, LinearMap.codRestrict_apply, DistribSMul.toLinearMap_apply] using hw
  ext h
  simp only [LinearMap.mem_ker, Submodule.mem_smul_pointwise_iff_exists,
    Submodule.mem_top, true_and]
  constructor
  · intro hh
    have hmem : ∀ p, h p ∈ N := fun p =>
      (Submodule.Quotient.mk_eq_zero N).mp (LinearMap.congr_fun hh p)
    obtain ⟨g, hg⟩ := Module.projective_lifting_property sx (h.codRestrict N hmem) hsx
    refine ⟨g, ?_⟩
    ext p
    have hp := congrArg Subtype.val (LinearMap.congr_fun hg p)
    simpa only [sx, LinearMap.comp_apply, LinearMap.codRestrict_apply,
      DistribSMul.toLinearMap_apply, LinearMap.smul_apply] using hp
  · rintro ⟨g, rfl⟩
    ext p
    simp only [LinearMap.compRight_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      Submodule.mkQ_apply, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
    exact (Submodule.mem_span_algebraMap_smul_iff ⊤ x).mpr ⟨g p, Submodule.mem_top, rfl⟩

end CommSemiring

variable [CommRing R] [Algebra R A] [Module R V] [IsScalarTower R A V]
  [Module.Projective A P]

variable (P x) in
/-- **Maps from a projective module into a reduction.** Let `A` be an algebra over a commutative
ring `R`, let `P` be a projective `A`-module, and let `x : R`. Composition with `V → V ⧸ x • V`
identifies the maps `P → V ⧸ x • V` with the reductions modulo `x` of the maps `P → V`: every
map lifts because `P` is projective, and a map with values in `x • V` is `x` times a map. -/
noncomputable def quotientSMulTopLinearMapEquiv :
    ((P →ₗ[A] V) ⧸ x • (⊤ : Submodule R (P →ₗ[A] V))) ≃ₗ[R]
      (P →ₗ[A] V ⧸ Ideal.span {algebraMap R A x} • (⊤ : Submodule A V)) :=
  (Submodule.quotEquivOfEq _ _
    (ker_compRight_mkQ_eq_smul_top_of_projective (x := x) P).symm).trans <|
    LinearMap.quotKerEquivOfSurjective _ (compRight_mkQ_surjective R P _)

@[simp]
theorem quotientSMulTopLinearMapEquiv_mk (f : P →ₗ[A] V) :
    quotientSMulTopLinearMapEquiv P x (Submodule.Quotient.mk f) =
      (Ideal.span {algebraMap R A x} • (⊤ : Submodule A V)).mkQ ∘ₗ f := by
  rw [quotientSMulTopLinearMapEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk, LinearMap.compRight_apply]

end Reduction

end TauCeti
