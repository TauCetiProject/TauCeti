/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.Transpose
public import TauCeti.Algebra.Module.Projective.Schanuel

/-!
# Morphisms of Auslander–Bridger transposes

A commutative square between presenting arrows induces a map between their transposes in the
opposite direction, by precomposing functional representatives. These maps preserve addition and
reverse composition. Every map between modules lifts to a square between their projective
presentations.

Different lifts of the same module map need not induce equal maps of transposes. Their difference
factors through `Hom_A(P₁, A)`, where `P₁` is the source of the first presenting arrow. The same
factorization holds for a lift of a module map factoring through a projective. For finitely
generated projective `P₁`, its dual is finitely generated projective over `Aᵐᵒᵖ`; thus these
factorizations are the lift independence and the vanishing on projective factorizations needed
to define the transpose on stable morphisms.

## Main results

* `TauCeti.AuslanderReitenTranspose.map`: the contravariant map induced by a presentation square.
* `TauCeti.exists_lift_projective_presentation`: a module map lifts to projective presentations.
* `TauCeti.AuslanderReitenTranspose.exists_map_sub_eq_mk_comp`: two lifts of the same module map
  differ through the dual of the first projective.
* `TauCeti.AuslanderReitenTranspose.exists_map_eq_mk_comp_of_factor`: a lift of a map factoring
  through a projective induces a map factoring through that dual.

## References

* M. Auslander, M. Bridger, *Stable module theory*, Mem. Amer. Math. Soc. 94 (1969), Section 2.1.
-/

public section

namespace TauCeti.AuslanderReitenTranspose

open LinearMap

variable {A : Type*} [Ring A]

section Squares

variable {P₀ P₁ Q₀ Q₁ : Type*}
  [AddCommMonoid P₀] [Module A P₀] [AddCommMonoid P₁] [Module A P₁]
  [AddCommMonoid Q₀] [Module A Q₀] [AddCommMonoid Q₁] [Module A Q₁]
  {p : P₁ →ₗ[A] P₀} {q : Q₁ →ₗ[A] Q₀}

/-- A commutative square from `p` to `q` induces an opposite-linear map from `Tr q` to `Tr p`.
On functional representatives it is precomposition with the map between the sources. -/
def map (f₀ : P₀ →ₗ[A] Q₀) (f₁ : P₁ →ₗ[A] Q₁) (hf : f₀ ∘ₗ p = q ∘ₗ f₁) :
    AuslanderReitenTranspose q →ₗ[Aᵐᵒᵖ] AuslanderReitenTranspose p :=
  lift q (mk p ∘ₗ f₁.lcomp Aᵐᵒᵖ A) fun φ => by
    have h : (q.lcomp Aᵐᵒᵖ A φ) ∘ₗ f₁ = p.lcomp Aᵐᵒᵖ A (φ ∘ₗ f₀) := by
      ext x
      exact congrArg φ (LinearMap.congr_fun hf x).symm
    simpa only [comp_apply, lcomp_apply'] using h ▸ mk_lcomp p (φ ∘ₗ f₀)

/-- The transpose map on functional representatives. -/
@[simp]
theorem map_mk (f₀ : P₀ →ₗ[A] Q₀) (f₁ : P₁ →ₗ[A] Q₁) (hf : f₀ ∘ₗ p = q ∘ₗ f₁)
    (φ : Module.Dual A Q₁) :
    map f₀ f₁ hf (mk q φ) = mk p (φ ∘ₗ f₁) := by
  simp [map, lcomp_apply']

/-- Precomposition followed by the quotient map is the transpose map followed by representatives. -/
@[simp]
theorem map_comp_mk (f₀ : P₀ →ₗ[A] Q₀) (f₁ : P₁ →ₗ[A] Q₁)
    (hf : f₀ ∘ₗ p = q ∘ₗ f₁) :
    map f₀ f₁ hf ∘ₗ mk q = mk p ∘ₗ f₁.lcomp Aᵐᵒᵖ A := by
  ext φ
  simp [lcomp_apply']

/-- The identity square induces the identity on the transpose. -/
@[simp]
theorem map_id : map (id : P₀ →ₗ[A] P₀) (id : P₁ →ₗ[A] P₁) (by simp) =
    (id : AuslanderReitenTranspose p →ₗ[Aᵐᵒᵖ] AuslanderReitenTranspose p) := by
  apply hom_ext p
  intro φ
  simp

/-- A square whose map between the sources vanishes induces zero on transposes. -/
@[simp]
theorem map_zero (f₀ : P₀ →ₗ[A] Q₀) (hf : f₀ ∘ₗ p = q ∘ₗ (0 : P₁ →ₗ[A] Q₁)) :
    map f₀ (0 : P₁ →ₗ[A] Q₁) hf =
      (0 : AuslanderReitenTranspose q →ₗ[Aᵐᵒᵖ] AuslanderReitenTranspose p) := by
  apply hom_ext q
  intro φ
  simp

/-- Transposition is additive on commutative squares. -/
@[simp]
theorem map_add (f₀ g₀ : P₀ →ₗ[A] Q₀) (f₁ g₁ : P₁ →ₗ[A] Q₁)
    (hf : f₀ ∘ₗ p = q ∘ₗ f₁) (hg : g₀ ∘ₗ p = q ∘ₗ g₁) :
    map (f₀ + g₀) (f₁ + g₁) (by simp [add_comp, comp_add, hf, hg]) =
      map f₀ f₁ hf + map g₀ g₁ hg := by
  apply hom_ext q
  intro φ
  simp [comp_add]

/-- Transposition reverses composition of commutative squares. -/
@[simp]
theorem map_comp_map {R₀ R₁ : Type*} [AddCommMonoid R₀] [Module A R₀]
    [AddCommMonoid R₁] [Module A R₁] {r : R₁ →ₗ[A] R₀}
    (f₀ : P₀ →ₗ[A] Q₀) (f₁ : P₁ →ₗ[A] Q₁) (hf : f₀ ∘ₗ p = q ∘ₗ f₁)
    (g₀ : Q₀ →ₗ[A] R₀) (g₁ : Q₁ →ₗ[A] R₁) (hg : g₀ ∘ₗ q = r ∘ₗ g₁) :
    map f₀ f₁ hf ∘ₗ map g₀ g₁ hg =
      map (g₀ ∘ₗ f₀) (g₁ ∘ₗ f₁) (by rw [comp_assoc, hf, ← comp_assoc, hg, comp_assoc]) := by
  apply hom_ext r
  intro φ
  simp [comp_assoc]

end Squares

section LiftIndependence

variable {P₀ P₁ Q₀ Q₁ : Type*}
  [AddCommMonoid P₀] [Module A P₀] [AddCommMonoid P₁] [Module A P₁]
  [AddCommGroup Q₀] [Module A Q₀] [AddCommGroup Q₁] [Module A Q₁]
  {p : P₁ →ₗ[A] P₀} {q : Q₁ →ₗ[A] Q₀}
  {N : Type*} [AddCommGroup N] [Module A N] {ρ : Q₀ →ₗ[A] N}

/-- Two presentation squares inducing the same map after augmentation have transpose maps
whose difference factors through the dual of `P₁`, with the final factor the quotient map.
When `P₁` is finite projective, this is independence on stable morphisms. -/
theorem exists_map_sub_eq_mk_comp [Module.Projective A P₀]
    (hq : Function.Exact q ρ) (f₀ g₀ : P₀ →ₗ[A] Q₀) (f₁ g₁ : P₁ →ₗ[A] Q₁)
    (hf : f₀ ∘ₗ p = q ∘ₗ f₁) (hg : g₀ ∘ₗ p = q ∘ₗ g₁)
    (hfg : ρ ∘ₗ f₀ = ρ ∘ₗ g₀) :
    ∃ h : AuslanderReitenTranspose q →ₗ[Aᵐᵒᵖ] Module.Dual A P₁,
      map f₀ f₁ hf - map g₀ g₁ hg = mk p ∘ₗ h := by
  have hrange : range (f₀ - g₀) ≤ range q := by
    rw [← LinearMap.exact_iff.mp hq]
    rintro _ ⟨x, rfl⟩
    simpa only [mem_ker, sub_apply, map_sub, sub_eq_zero, comp_apply] using
      LinearMap.congr_fun hfg x
  obtain ⟨s, hs⟩ := exists_comp_eq_of_range_le hrange
  let t := f₁ - g₁ - s ∘ₗ p
  have ht : q ∘ₗ t = 0 := by
    simp [t, comp_sub, ← hf, ← hg, ← comp_assoc, hs, sub_comp]
  let h : AuslanderReitenTranspose q →ₗ[Aᵐᵒᵖ] Module.Dual A P₁ :=
    lift q (t.lcomp Aᵐᵒᵖ A) fun φ => by
      ext x
      simpa [lcomp_apply'] using congrArg φ (LinearMap.congr_fun ht x)
  refine ⟨h, ?_⟩
  apply hom_ext q
  intro φ
  have hrep : φ ∘ₗ t = (φ ∘ₗ f₁ - φ ∘ₗ g₁) - p.lcomp Aᵐᵒᵖ A (φ ∘ₗ s) := by
    simp [t, comp_sub, comp_assoc, lcomp_apply']
  simp only [sub_apply, map_mk, comp_apply, h, lift_mk, lcomp_apply']
  rw [hrep, map_sub, map_sub, mk_lcomp, sub_zero]

/-- If a module map factors through a projective, any lift to presentations induces a transpose
map factoring through the dual of `P₁`. No minimality or finiteness is required. -/
theorem exists_map_eq_mk_comp_of_factor [Module.Projective A P₀]
    {M C : Type*} [AddCommMonoid M] [Module A M] [AddCommMonoid C] [Module A C]
    [Module.Projective A C] {π : P₀ →ₗ[A] M}
    (hp : π ∘ₗ p = 0) (hq : Function.Exact q ρ) (hρ : Function.Surjective ρ)
    (i : M →ₗ[A] C) (j : C →ₗ[A] N)
    (f₀ : P₀ →ₗ[A] Q₀) (f₁ : P₁ →ₗ[A] Q₁) (hf : f₀ ∘ₗ p = q ∘ₗ f₁)
    (hfactor : ρ ∘ₗ f₀ = j ∘ₗ i ∘ₗ π) :
    ∃ h : AuslanderReitenTranspose q →ₗ[Aᵐᵒᵖ] Module.Dual A P₁,
      map f₀ f₁ hf = mk p ∘ₗ h := by
  obtain ⟨b, hb⟩ := Module.projective_lifting_property ρ j hρ
  have hzero : (b ∘ₗ i ∘ₗ π) ∘ₗ p = q ∘ₗ (0 : P₁ →ₗ[A] Q₁) := by
    simp [comp_assoc, hp]
  obtain ⟨h, hh⟩ := exists_map_sub_eq_mk_comp hq f₀ (b ∘ₗ i ∘ₗ π) f₁ 0 hf hzero
    (by simpa [← comp_assoc, hb] using hfactor)
  exact ⟨h, by simpa using hh⟩

end LiftIndependence

end TauCeti.AuslanderReitenTranspose
