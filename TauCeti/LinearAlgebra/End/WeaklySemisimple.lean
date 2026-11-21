/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.LinearMap.Ker
public import TauCeti.LinearAlgebra.LinearMap.Range
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Noetherian.Orzech

/-!
# Weak semisimplicity at eigenvalue one

For an endomorphism `σ`, the canonical map from `ker (σ - id)` to `coker (σ - id)`
is bijective exactly when the kernel and image of `σ - id` are complementary.
This is the algebraic weak-semisimplicity criterion, not semisimplicity at all eigenvalues.
On a Noetherian module, surjectivity alone implies bijectivity. These criteria provide
the linear algebra for lifting weak semisimplicity from residual representations.

The terminology follows Liu–Tian–Xiao–Zhang–Zhu, *On the Beilinson–Bloch–Kato
conjecture for Rankin–Selberg motives*, Definition 2.1.2 and Lemma 2.1.3, pp. 121–122.
No topological identification with continuous procyclic coinvariants is asserted here.
-/

public section

namespace LinearMap

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- Inclusion of the fixed vectors of `σ`, followed by projection to its coinvariants. -/
def invariantCoinvariantMap (σ : M →ₗ[R] M) :
    ker (σ - id) →ₗ[R] M ⧸ range (σ - id) :=
  (range (σ - id)).mkQ.comp (ker (σ - id)).subtype

/-- Weak semisimplicity at eigenvalue one: fixed vectors map bijectively to coinvariants. -/
def IsWeaklySemisimple (σ : M →ₗ[R] M) : Prop :=
  Function.Bijective σ.invariantCoinvariantMap

/-- The canonical map sends a fixed vector to its quotient class. -/
@[simp]
theorem invariantCoinvariantMap_apply (σ : M →ₗ[R] M) (x : ker (σ - id)) :
    σ.invariantCoinvariantMap x = (range (σ - id)).mkQ (x : M) :=
  (rfl)

/-- Injectivity means that no nonzero fixed vector is in the image of `σ - id`. -/
theorem invariantCoinvariantMap_injective_iff (σ : M →ₗ[R] M) :
    Function.Injective σ.invariantCoinvariantMap ↔ Disjoint (ker (σ - id)) (range (σ - id)) := by
  simpa [invariantCoinvariantMap, domRestrict] using
    (injective_domRestrict_iff (f := (range (σ - id)).mkQ) (S := ker (σ - id)))

/-- Surjectivity means that fixed vectors and the image of `σ - id` span the module. -/
theorem invariantCoinvariantMap_surjective_iff (σ : M →ₗ[R] M) :
    Function.Surjective σ.invariantCoinvariantMap ↔
      Codisjoint (ker (σ - id)) (range (σ - id)) := by
  rw [← range_eq_top, invariantCoinvariantMap, range_comp, Submodule.range_subtype,
    Submodule.map_mkQ_eq_top, sup_comm, ← codisjoint_iff]

/-- Weak semisimplicity is precisely the kernel/image direct decomposition. -/
theorem isWeaklySemisimple_iff_isCompl (σ : M →ₗ[R] M) :
    σ.IsWeaklySemisimple ↔ IsCompl (ker (σ - id)) (range (σ - id)) := by
  rw [IsWeaklySemisimple, Function.Bijective, invariantCoinvariantMap_injective_iff,
    invariantCoinvariantMap_surjective_iff, isCompl_iff]

/-- The identity endomorphism is weakly semisimple, on any module. -/
@[simp]
theorem isWeaklySemisimple_id : (id : M →ₗ[R] M).IsWeaklySemisimple := by
  rw [isWeaklySemisimple_iff_isCompl]
  simpa using (isCompl_top_bot : IsCompl (⊤ : Submodule R M) ⊥)

/-- If `σ - id` is invertible, there are neither fixed vectors nor coinvariants. -/
theorem isWeaklySemisimple_of_bijective_sub_id (σ : M →ₗ[R] M)
    (hσ : Function.Bijective (σ - id : M →ₗ[R] M)) : σ.IsWeaklySemisimple := by
  rw [isWeaklySemisimple_iff_isCompl, ker_eq_bot.mpr hσ.1, range_eq_top.mpr hσ.2]
  exact isCompl_bot_top

section Equivalence

variable {N : Type*} [AddCommGroup N] [Module R N]

/-- An intertwining linear equivalence preserves weak semisimplicity. -/
theorem isWeaklySemisimple_iff_of_equiv (σ : M →ₗ[R] M) {τ : N →ₗ[R] N}
    (e : M ≃ₗ[R] N) (h : τ.comp e.toLinearMap = e.toLinearMap.comp σ) :
    σ.IsWeaklySemisimple ↔ τ.IsWeaklySemisimple := by
  have hsub : (τ - id).comp e.toLinearMap = e.toLinearMap.comp (σ - id) := by
    simp [comp_sub, sub_comp, h]
  rw [σ.isWeaklySemisimple_iff_isCompl, τ.isWeaklySemisimple_iff_isCompl,
    ← (σ - id : M →ₗ[R] M).map_ker_eq_ker_of_comp_eq e.surjective e.injective hsub,
    ← (σ - id : M →ₗ[R] M).map_range_eq_range_of_comp_eq e.surjective hsub]
  exact (Submodule.orderIsoMapComap e).isCompl_iff

/-- A direct sum of two endomorphisms is weakly semisimple exactly when both are. -/
@[simp]
theorem isWeaklySemisimple_prodMap_iff (σ : M →ₗ[R] M) (τ : N →ₗ[R] N) :
    (σ.prodMap τ).IsWeaklySemisimple ↔ σ.IsWeaklySemisimple ∧ τ.IsWeaklySemisimple := by
  have hsub : σ.prodMap τ - id = (σ - id).prodMap (τ - id) := by
    ext <;> simp
  simp only [isWeaklySemisimple_iff_isCompl, hsub, ker_prodMap, range_prodMap,
    isCompl_iff, disjoint_iff, codisjoint_iff, Submodule.prod_inf_prod,
    Submodule.prod_sup_prod, Submodule.prod_eq_bot_iff, Submodule.prod_eq_top_iff]
  tauto

end Equivalence

section RestrictScalars

variable (R) {S : Type*} [Ring S] [SMul R S] [Module S M] [IsScalarTower R S M]

/-- Weak semisimplicity is unchanged on forgetting part of the coefficient action. -/
@[simp]
theorem isWeaklySemisimple_restrictScalars_iff (σ : M →ₗ[S] M) :
    (σ.restrictScalars R).IsWeaklySemisimple ↔ σ.IsWeaklySemisimple := by
  have hsub : σ.restrictScalars R - id = (σ - id).restrictScalars R := by
    ext
    rfl
  simp only [isWeaklySemisimple_iff_isCompl, hsub, ker_restrictScalars,
    range_restrictScalars, Submodule.isCompl_restrictScalars_iff]

end RestrictScalars

section Noetherian

variable [IsNoetherian R M]

/-- On a Noetherian module, surjectivity from invariants to coinvariants implies
weak semisimplicity. No freeness or field hypothesis is needed. -/
theorem isWeaklySemisimple_of_surjective_invariantCoinvariantMap (σ : M →ₗ[R] M)
    (hσ : Function.Surjective σ.invariantCoinvariantMap) : σ.IsWeaklySemisimple := by
  let f := σ - id
  have hspan := σ.invariantCoinvariantMap_surjective_iff.mp hσ
  let g : range f →ₗ[R] range f := f.rangeRestrict.domRestrict (range f)
  have hsurj : Function.Surjective g := by
    rintro ⟨_, x, rfl⟩
    obtain ⟨a, b, ha, hb, hab⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hspan x
    refine ⟨⟨b, hb⟩, Subtype.ext ?_⟩
    have ha0 : f a = 0 := mem_ker.mp ha
    simp [g, ← hab, ha0]
  -- The moving part is Noetherian, so its surjective endomorphism is injective.
  have hinj := IsNoetherian.injective_of_surjective_endomorphism g hsurj
  apply σ.isWeaklySemisimple_iff_isCompl.mpr
  refine ⟨Submodule.disjoint_def.mpr ?_, hspan⟩
  intro x hx hy
  have hx0 : f x = 0 := mem_ker.mp hx
  have hzero : g ⟨x, hy⟩ = g 0 := Subtype.ext (by simp [g, hx0])
  exact congrArg Subtype.val (hinj hzero)

/-- On a Noetherian module, testing surjectivity of the canonical map suffices. -/
theorem isWeaklySemisimple_iff_surjective_invariantCoinvariantMap (σ : M →ₗ[R] M) :
    σ.IsWeaklySemisimple ↔ Function.Surjective σ.invariantCoinvariantMap :=
  ⟨fun hσ => hσ.2, σ.isWeaklySemisimple_of_surjective_invariantCoinvariantMap⟩

end Noetherian

-- The unipotent Jordan block fails the criterion over every nonzero coefficient ring.
example [Nontrivial R] :
    ¬ (id + (inl R R R).comp (snd R R R) : (R × R) →ₗ[R] R × R).IsWeaklySemisimple := by
  let σ : (R × R) →ₗ[R] R × R := id + (inl R R R).comp (snd R R R)
  intro hσ
  have hdis := (σ.isWeaklySemisimple_iff_isCompl.mp hσ).disjoint
  have hz := Submodule.disjoint_def.mp hdis (1, 0) (by simp [σ])
    ⟨(0, 1), by simp [σ]⟩
  exact one_ne_zero (congrArg Prod.fst hz)

end LinearMap
