/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.Functor
public import TauCeti.LinearAlgebra.Dual.Opposite

/-!
# Fullness of the stable transpose

Every map between transposes of finite projective presentations is induced by a square
between the original presentations. Consequently the contravariant transpose functor on
finitely presented stable modules is full. This is the fullness half of the
Auslander–Bridger stable duality; faithfulness and essential surjectivity are separate results.

The lifting statement is stronger than stable fullness: it realizes an actual module map
between transposes, before passing to the projective stable quotient. Neither minimality
nor a Noetherian hypothesis is needed, and the coefficient ring may be noncommutative.

The proof uses the opposite-dual evaluation equivalence from
`TauCeti.LinearAlgebra.Dual.Opposite` to recover a presentation square from a square between
its duals, and the existing presentation-lifting theorem to produce the latter square.

## References

* M. Auslander, M. Bridger, *Stable module theory*, Section 2.1.
-/

public section

namespace TauCeti

open CategoryTheory LinearMap

universe u v

variable {A : Type u} [Ring A]

namespace AuslanderReitenTranspose

section Lifts

variable {M : Type*} {N : Type*} {P₀ : Type*} {P₁ : Type*} {Q₀ : Type*} {Q₁ : Type*}
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  [AddCommGroup P₀] [Module A P₀] [AddCommGroup P₁] [Module A P₁]
  [AddCommGroup Q₀] [Module A Q₀] [AddCommGroup Q₁] [Module A Q₁]
  [Module.Projective A Q₀] [Module.Finite A Q₀]
  [Module.Projective A Q₁] [Module.Finite A Q₁]
  {p : P₁ →ₗ[A] P₀} {q : Q₁ →ₗ[A] Q₀} {π : P₀ →ₗ[A] M} {ρ : Q₀ →ₗ[A] N}

/-- Every map `Tr q → Tr p`, with `q` an arrow between finite projectives, comes from a
square from `p` to `q`. The modules of `p` are arbitrary. This is an equality of actual module
maps, not merely of stable classes. -/
theorem exists_map_eq (h : AuslanderReitenTranspose q →ₗ[Aᵐᵒᵖ] AuslanderReitenTranspose p) :
    ∃ (f₀ : P₀ →ₗ[A] Q₀) (f₁ : P₁ →ₗ[A] Q₁)
      (hf : f₀ ∘ₗ p = q ∘ₗ f₁), map f₀ f₁ hf = h := by
  have hp : Function.Exact (p.lcomp Aᵐᵒᵖ A) (mk p) := by
    rw [LinearMap.exact_iff, ker_mk]
  obtain ⟨g₀, g₁, hg₀, hg₁⟩ := exists_lift_projective_presentation
    (p := q.lcomp Aᵐᵒᵖ A) (π := mk q)
    (by ext φ; simp) hp (mk_surjective p) h
  obtain ⟨f₁, rfl⟩ := (opDual_lcomp_bijective (A := A) (P := Q₁) (Q := P₁)).surjective g₀
  obtain ⟨f₀, rfl⟩ := (opDual_lcomp_bijective (A := A) (P := Q₀) (Q := P₀)).surjective g₁
  have hf : f₀ ∘ₗ p = q ∘ₗ f₁ := by
    apply (opDual_lcomp_bijective (A := A) (P := Q₀) (Q := P₁)).injective
    ext φ x
    exact (LinearMap.congr_fun (LinearMap.congr_fun hg₁ φ) x).symm
  refine ⟨f₀, f₁, hf, ?_⟩
  apply hom_ext q
  intro φ
  simpa only [map_mk, LinearMap.comp_apply, lcomp_apply'] using LinearMap.congr_fun hg₀ φ

/-- A map `Tr q → Tr p` is the transpose of a lift of some map between the presented
modules, provided the modules of `q` are finite projective. The diagram ending in `M`
need only be exact and surjective, and the diagram ending in `N` need only have zero composite. -/
theorem exists_lift_map_eq (hp : Function.Exact p π) (hπ : Function.Surjective π)
    (h : AuslanderReitenTranspose q →ₗ[Aᵐᵒᵖ] AuslanderReitenTranspose p)
    (hq : ρ ∘ₗ q = 0) :
    ∃ (f : M →ₗ[A] N) (f₀ : P₀ →ₗ[A] Q₀) (f₁ : P₁ →ₗ[A] Q₁)
      (_hf₀ : ρ ∘ₗ f₀ = f ∘ₗ π) (hf₁ : f₀ ∘ₗ p = q ∘ₗ f₁), map f₀ f₁ hf₁ = h := by
  obtain ⟨f₀, f₁, hf₁, hh⟩ := exists_map_eq h
  have hker : LinearMap.ker π ≤ LinearMap.ker (ρ ∘ₗ f₀) := by
    rw [hp.linearMap_ker_eq]
    rintro _ ⟨x, rfl⟩
    simp only [mem_ker, LinearMap.comp_apply]
    have hzero : (ρ ∘ₗ f₀) ∘ₗ p = 0 := by
      rw [LinearMap.comp_assoc, hf₁, ← LinearMap.comp_assoc, hq]
      simp
    exact LinearMap.congr_fun hzero x
  let f := π.liftOfSurjective hπ ⟨ρ ∘ₗ f₀, hker⟩
  refine ⟨f, f₀, f₁, ?_, hf₁, hh⟩
  ext x
  exact (LinearMap.equivOfSurjective_apply hπ hker).symm

end Lifts

variable {M N P₀ P₁ Q₀ Q₁ : Type v}
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  [AddCommGroup P₀] [Module A P₀] [AddCommGroup P₁] [Module A P₁]
  [AddCommGroup Q₀] [Module A Q₀] [AddCommGroup Q₁] [Module A Q₁]
  [Module.Projective A P₀] [Module.Projective A P₁] [Module.Finite A P₁]
  [Module.Projective A Q₀] [Module.Finite A Q₀]
  [Module.Projective A Q₁] [Module.Finite A Q₁]
  {p : P₁ →ₗ[A] P₀} {q : Q₁ →ₗ[A] Q₀} {π : P₀ →ₗ[A] M} {ρ : Q₀ →ₗ[A] N}

local notation "S" => ExactStructure.projectiveStableFunctor (ExactStructure.abelian (ModuleCat A))
local notation "T" =>
  ExactStructure.projectiveStableFunctor (ExactStructure.abelian (ModuleCat Aᵐᵒᵖ))

/-- Transposition is surjective on stable Hom groups for finite projective presentations. -/
theorem stableMap_surjective [Small.{v} A]
    (hp : Function.Exact p π) (hπ : Function.Surjective π)
    (hq : Function.Exact q ρ) (hρ : Function.Surjective ρ) :
    Function.Surjective (stableMap hp.linearMap_comp_eq_zero hq hρ) := by
  intro h
  obtain ⟨h, rfl⟩ := (T).map_surjective h
  obtain ⟨f, f₀, f₁, hf₀, hf₁, hh⟩ := exists_lift_map_eq hp hπ h.hom hq.linearMap_comp_eq_zero
  refine ⟨(S).map (ModuleCat.ofHom f), ?_⟩
  rw [stableMap_quotient_map hp.linearMap_comp_eq_zero hq hρ f f₀ f₁ hf₀ hf₁, hh,
    ModuleCat.ofHom_hom]

end AuslanderReitenTranspose

variable (P : ∀ M : FinitelyPresentedStableModule.{u, max u v} A,
  FiniteProjectivePresentation M.obj.as)

/-- The stable transpose functor attached to any family of finite projective presentations
is full. -/
instance : (stableTransposeFunctor P).Full where
  map_surjective {M N} h := by
    let h' : Opposite.op (P M).stableTransposeObj ⟶ Opposite.op (P N).stableTransposeObj :=
      eqToHom (stableTransposeFunctor_obj P M).symm ≫ h ≫
        eqToHom (stableTransposeFunctor_obj P N)
    obtain ⟨f, hf⟩ := AuslanderReitenTranspose.stableMap_surjective
      (P M).exact (P M).surjective (P N).exact (P N).surjective h'.unop.hom
    have heq : (ObjectProperty.homMk
        (AuslanderReitenTranspose.stableMap (P M).exact.linearMap_comp_eq_zero
          (P N).exact (P N).surjective f)).op = h' := by
      apply Quiver.Hom.unop_inj
      apply ObjectProperty.hom_ext
      exact hf
    refine ⟨ObjectProperty.homMk f, ?_⟩
    rw [stableTransposeFunctor_map, ObjectProperty.homMk_hom, heq]
    simp [h']

/-- The Auslander–Bridger transpose with chosen presentations is full. -/
instance : (stableTranspose.{u, v} A).Full := by
  rw [stableTranspose_def]
  infer_instance

end TauCeti
