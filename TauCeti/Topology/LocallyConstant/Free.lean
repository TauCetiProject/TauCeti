/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.Topology.Category.Profinite.Nobeling.Induction
public import Mathlib.Topology.DiscreteQuotient
public import TauCeti.Topology.DiscreteQuotient
public import TauCeti.Topology.LocallyConstant.Algebra

/-!
# Locally constant functions on a profinite set form a free module

For a compact space `X`, a commutative semiring `R` and an `R`-module `N`, the locally constant
`N`-valued functions on `X` are the base change of the `R`-valued ones:
`N ⊗[R] LocallyConstant X R ≃ LocallyConstant X N`, by `n ⊗ f ↦ (x ↦ f x • n)`. Every locally
constant function on a compact space factors through a finite discrete quotient of `X`, and
for functions on a finite set this is `TensorProduct.piScalarRight`. Compactness is needed: on
`ℕ` with the discrete topology, the image of `ℚ ⊗[ℤ] LocallyConstant ℕ ℤ` consists of functions
with bounded denominators, so it misses `n ↦ 1 / (n + 1)` in `LocallyConstant ℕ ℚ`.

For a profinite set `S`, Nöbeling's theorem (`LocallyConstant.freeOfProfinite`) makes
`LocallyConstant S ℤ` a free abelian group, so by base change `C⁰(S, Λ) = LocallyConstant S Λ` is
a free `Λ`-module for every commutative ring `Λ`; in particular tensoring with it is exact. This
is the coefficient module of compactly supported cohomology along a projection `Y × S → Y`, and
its `Λ`-linear dual is the module of `Λ`-valued distributions on `S`. When `S` is finite and
discrete and `Λ` is nontrivial (more generally, has the strong rank condition),
`C⁰(S, Λ) = Λ^S` has rank the cardinality of `S`; for a nontrivial ring `Λ`, `C⁰(S, Λ)` is
finitely generated only when `S` is finite.

## Main definitions and results

* `TauCeti.locallyConstantScalarRightHom`: the natural map
  `N ⊗[R] LocallyConstant X R →ₗ[S] LocallyConstant X N`.
* `TauCeti.locallyConstantScalarRight`: for compact `X`, this map is a linear equivalence.
* `TauCeti.instModuleFreeLocallyConstant`: `LocallyConstant S Λ` is a free `Λ`-module for a
  profinite set `S` and a commutative ring `Λ`.
* `TauCeti.finrank_locallyConstant_eq_natCard`: on a finite discrete space the rank over a ring
  with the strong rank condition is the number of points.
* `TauCeti.finite_locallyConstant_self_iff`: for a profinite set `S`, `LocallyConstant S Λ` is
  finitely generated exactly when `Λ` is the zero ring or `S` is finite.

## References

* G. Nöbeling, *Verallgemeinerung eines Satzes von Herrn E. Specker*, Invent. Math. 6 (1968).
* P. Scholze, *Étale cohomology of diamonds*, proof of Lemma 23.6.
-/

public section

open TensorProduct

namespace TauCeti

section ScalarRight

variable (R : Type*) [CommSemiring R] (S : Type*) [CommSemiring S] [Algebra R S]
  (N : Type*) [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]
  (X : Type*) [TopologicalSpace X]

/-- The bilinear map `(n, f) ↦ (x ↦ f x • n)` underlying `locallyConstantScalarRightHom`. -/
private def locallyConstantScalarRightHomBil :
    N →ₗ[S] LocallyConstant X R →ₗ[R] LocallyConstant X N where
  toFun n := LocallyConstant.mapₗ R (LinearMap.toSpanSingleton R N n)
  map_add' x y := by
    ext f a
    simp
  map_smul' s x := by
    ext f a
    simpa using smul_comm (f a) s x

/-- The natural map `N ⊗[R] LocallyConstant X R → LocallyConstant X N`, sending `n ⊗ f` to the
function `x ↦ f x • n`. For compact `X` it is a linear equivalence,
`locallyConstantScalarRight`. -/
def locallyConstantScalarRightHom : N ⊗[R] LocallyConstant X R →ₗ[S] LocallyConstant X N :=
  AlgebraTensorModule.lift (locallyConstantScalarRightHomBil R S N X)

variable {R S N X}

@[simp]
theorem locallyConstantScalarRightHom_tmul_apply (n : N) (f : LocallyConstant X R) (x : X) :
    locallyConstantScalarRightHom R S N X (n ⊗ₜ f) x = f x • n := by
  simp [locallyConstantScalarRightHom, locallyConstantScalarRightHomBil]

/-- On tensors pulled back from a discrete quotient `Q`, `locallyConstantScalarRightHom` is
`TensorProduct.piScalarRightHom` for the finite index type `Q`, pulled back along `Q.proj`. -/
private theorem locallyConstantScalarRightHom_lTensor (Q : DiscreteQuotient X)
    (t : N ⊗[R] (Q → R)) :
    locallyConstantScalarRightHom R S N X ((Q.proj_isLocallyConstant.funLeft R R).lTensor N t) =
      Q.proj_isLocallyConstant.funLeft S N (piScalarRightHom R S N Q t) := by
  induction t using TensorProduct.inductionOn with
  | tmul n g => ext; simp
  | add t₁ t₂ h₁ h₂ => simp only [map_add, h₁, h₂]

/-- A tensor pulled back from a discrete quotient `Q'` is also pulled back from every finer
discrete quotient `Q`. -/
private theorem lTensor_funLeft_proj_of_le {Q Q' : DiscreteQuotient X} (h : Q ≤ Q')
    (t : N ⊗[R] (Q' → R)) :
    (Q'.proj_isLocallyConstant.funLeft R R).lTensor N t =
      (Q.proj_isLocallyConstant.funLeft R R).lTensor N
        ((LinearMap.funLeft R R (DiscreteQuotient.ofLE h)).lTensor N t) := by
  simp only [← LinearMap.lTensor_comp_apply, ← IsLocallyConstant.funLeft_comp,
    DiscreteQuotient.ofLE_comp_proj]

/-- Every tensor in `N ⊗[R] LocallyConstant X R` is pulled back from some discrete quotient. -/
private theorem exists_eq_lTensor_funLeft_proj (t : N ⊗[R] LocallyConstant X R) :
    ∃ (Q : DiscreteQuotient X) (t' : N ⊗[R] (Q → R)),
      (Q.proj_isLocallyConstant.funLeft R R).lTensor N t' = t := by
  induction t using TensorProduct.inductionOn with
  | tmul n f =>
    refine ⟨f.discreteQuotient, n ⊗ₜ f.lift, ?_⟩
    rw [LinearMap.lTensor_tmul, LocallyConstant.funLeft_lift]
  | add t₁ t₂ h₁ h₂ =>
    obtain ⟨Q₁, t₁, rfl⟩ := h₁
    obtain ⟨Q₂, t₂, rfl⟩ := h₂
    refine ⟨Q₁ ⊓ Q₂, (LinearMap.funLeft R R (DiscreteQuotient.ofLE inf_le_left)).lTensor N t₁ +
      (LinearMap.funLeft R R (DiscreteQuotient.ofLE inf_le_right)).lTensor N t₂, ?_⟩
    rw [map_add, ← lTensor_funLeft_proj_of_le, ← lTensor_funLeft_proj_of_le]

variable (R S N X)

/-- On a compact space, `n ⊗ f ↦ (x ↦ f x • n)` is a bijection
`N ⊗[R] LocallyConstant X R → LocallyConstant X N`. -/
theorem locallyConstantScalarRightHom_bijective [CompactSpace X] :
    Function.Bijective (locallyConstantScalarRightHom R S N X) := by
  classical
  refine ⟨fun t₁ t₂ h ↦ ?_, fun g ↦ ?_⟩
  · obtain ⟨Q₁, t₁, rfl⟩ := exists_eq_lTensor_funLeft_proj (R := R) (N := N) t₁
    obtain ⟨Q₂, t₂, rfl⟩ := exists_eq_lTensor_funLeft_proj (R := R) (N := N) t₂
    rw [lTensor_funLeft_proj_of_le (inf_le_left : Q₁ ⊓ Q₂ ≤ Q₁),
      lTensor_funLeft_proj_of_le (inf_le_right : Q₁ ⊓ Q₂ ≤ Q₂)] at h ⊢
    have := Fintype.ofFinite ↥(Q₁ ⊓ Q₂)
    rw [locallyConstantScalarRightHom_lTensor, locallyConstantScalarRightHom_lTensor] at h
    have h' := (Q₁ ⊓ Q₂).proj_isLocallyConstant.funLeft_injective
      (Q₁ ⊓ Q₂).proj_surjective S N h
    rw [← piScalarRight_apply, ← piScalarRight_apply] at h'
    rw [(piScalarRight R S N _).injective h']
  · have := Fintype.ofFinite g.discreteQuotient
    refine ⟨(g.discreteQuotient.proj_isLocallyConstant.funLeft R R).lTensor N
      ((piScalarRight R S N _).symm g.lift), ?_⟩
    rw [locallyConstantScalarRightHom_lTensor, ← piScalarRight_apply,
      LinearEquiv.apply_symm_apply]
    exact LocallyConstant.funLeft_lift S g

/-- For a compact space `X`, `N ⊗[R] LocallyConstant X R` is canonically isomorphic to
`LocallyConstant X N`, by `n ⊗ f ↦ (x ↦ f x • n)`. -/
noncomputable def locallyConstantScalarRight [CompactSpace X] :
    N ⊗[R] LocallyConstant X R ≃ₗ[S] LocallyConstant X N :=
  .ofBijective _ (locallyConstantScalarRightHom_bijective R S N X)

@[simp]
theorem locallyConstantScalarRight_apply [CompactSpace X] (t : N ⊗[R] LocallyConstant X R) :
    locallyConstantScalarRight R S N X t = locallyConstantScalarRightHom R S N X t :=
  (rfl)

end ScalarRight

section Free

/-- Nöbeling's theorem with coefficients: for a profinite set `S` and a commutative ring `Λ`,
the locally constant functions `S → Λ` form a free `Λ`-module. -/
instance instModuleFreeLocallyConstant (Λ : Type*) [CommRing Λ] (S : Type*) [TopologicalSpace S]
    [CompactSpace S] [T2Space S] [TotallyDisconnectedSpace S] :
    Module.Free Λ (LocallyConstant S Λ) :=
  have : Module.Free ℤ (LocallyConstant S ℤ) := LocallyConstant.freeOfProfinite (.of S)
  .of_equiv (locallyConstantScalarRight ℤ Λ Λ S)

/-- On a finite discrete space `S`, `LocallyConstant S Λ = Λ ^ S` has rank the number of points
of `S`, for a ring `Λ` with the strong rank condition (for instance any nontrivial commutative
ring). -/
theorem finrank_locallyConstant_eq_natCard (Λ : Type*) [Ring Λ] [StrongRankCondition Λ]
    (S : Type*) [TopologicalSpace S] [DiscreteTopology S] [Finite S] :
    Module.finrank Λ (LocallyConstant S Λ) = Nat.card S := by
  have := Fintype.ofFinite S
  rw [(LocallyConstant.linearEquivFnOfDiscrete Λ).finrank_eq, Module.finrank_pi,
    Nat.card_eq_fintype_card]

/-- For a profinite set `S`, the module `LocallyConstant S Λ` is finitely generated exactly when
`Λ` is the zero ring or `S` is finite. -/
theorem finite_locallyConstant_self_iff (Λ : Type*) [CommRing Λ] (S : Type*)
    [TopologicalSpace S] [CompactSpace S] [T2Space S] [TotallyDisconnectedSpace S] :
    Module.Finite Λ (LocallyConstant S Λ) ↔ Subsingleton Λ ∨ Finite S := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rw [or_iff_not_imp_left, not_subsingleton_iff_nontrivial, ← not_infinite_iff_finite]
    intro _ _
    obtain ⟨Q, hQ⟩ := DiscreteQuotient.exists_lt_natCard (X := S)
      (Module.finrank Λ (LocallyConstant S Λ))
    have := Fintype.ofFinite Q
    have hle := LinearMap.finrank_le_finrank_of_injective
      (Q.proj_isLocallyConstant.funLeft_injective Q.proj_surjective Λ Λ)
    rw [Module.finrank_pi, ← Nat.card_eq_fintype_card] at hle
    omega
  · rintro (_ | _)
    · have := Module.subsingleton Λ (LocallyConstant S Λ)
      infer_instance
    · have := Fintype.ofFinite S
      exact .equiv (LocallyConstant.linearEquivFnOfDiscrete Λ).symm

end Free

end TauCeti

