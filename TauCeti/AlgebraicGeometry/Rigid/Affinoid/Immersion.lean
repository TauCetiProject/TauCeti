/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Rigid.Affinoid.Stalk.Map

import TauCeti.RingTheory.Finiteness.Nakayama
import TauCeti.RingTheory.Jacobson.Ring

/-!
# Locally closed and open immersions of affinoid spaces

A `K`-algebra map `φ : A → B` of affinoid algebras is a morphism `Sp B → Sp A`. It is a
*locally closed immersion* (`TauCeti.IsAffinoidLocallyClosedImmersion`) if it is injective on
classical points and every stalk map `φ*_y : 𝒪_{Sp A,φ(y)} → 𝒪_{Sp B,y}` is surjective, and an
*open immersion* (`TauCeti.IsAffinoidOpenImmersion`) if it is injective on classical points and
every stalk map is bijective. Like affinoid subdomains and Runge immersions, both notions are
algebraic: no norm on `A` or `B` is chosen. The names carry `Affinoid` to keep them apart from
Mathlib's scheme-theoretic `AlgebraicGeometry.IsOpenImmersion`.

The inclusion of an affinoid subdomain is an open immersion, since it induces isomorphisms of
stalks; in particular the identity is one. Open immersions are locally closed immersions, and both
classes are closed under composition. A locally closed immersion whose algebra map `φ` is finite
is a closed immersion, that is, `φ` is surjective: for a maximal ideal `𝔪ₓ` of `A`, the ideal
`𝔪ₓ B` lies in no maximal ideal other than that of the unique point `y` over `x` (if there is
one), so it contains a power `𝔪_yⁿ` as `B` is a Jacobson ring, and surjectivity of the stalk map
at `y` gives `B = φ(A) + 𝔪_yⁿ ⊆ φ(A) + 𝔪ₓ B`. Nakayama's lemma, applied at every maximal ideal to
the finite `A`-module `B ⧸ φ(A)`, shows that it vanishes.

Injectivity on points is not implied by the stalk condition: the diagonal `K → K × K` has
bijective stalk maps at both points of `Sp (K × K)` but maps them to the single point of `Sp K`.
Surjectivity of the stalk maps is not implied by injectivity on points either: the normalisation
`K⟨X, Y⟩ ⧸ (Y² - X³) → K⟨t⟩` of the cusp, `X ↦ t²`, `Y ↦ t³`, is injective on classical points,
but its stalk map at the origin misses `t`.

## Main definitions

* `TauCeti.IsAffinoidLocallyClosedImmersion φ`: `Sp B → Sp A` is a locally closed immersion.
* `TauCeti.IsAffinoidOpenImmersion φ`: `Sp B → Sp A` is an open immersion.

## Main results

* `TauCeti.IsAffinoidSubdomainMap.isAffinoidOpenImmersion`: inclusions of affinoid subdomains
  are open immersions.
* `TauCeti.IsAffinoidOpenImmersion.isAffinoidLocallyClosedImmersion`: open immersions are locally
  closed.
* `TauCeti.IsAffinoidLocallyClosedImmersion.comp`, `TauCeti.IsAffinoidOpenImmersion.comp`: both
  classes are closed under composition.
* `TauCeti.IsAffinoidLocallyClosedImmersion.surjective_of_finite`: a finite locally closed
  immersion is a closed immersion.

## References

* S. Bosch, *Lectures on Formal and Rigid Geometry*, Lecture Notes in Mathematics 2105,
  Springer, 2014, §4.2, Definition 1, p. 69, and Proposition 3, pp. 70–71.
-/

public section

namespace TauCeti

universe u

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
  [CommRing C] [Algebra K C]
  [hA : Fact (IsAffinoidAlgebra K A)] [hB : Fact (IsAffinoidAlgebra K B)]
  [hC : Fact (IsAffinoidAlgebra K C)]

/-- **Locally closed immersions of affinoid spaces.** The morphism `Sp B → Sp A` given by
`φ : A → B` is a locally closed immersion if it is injective on classical points and every stalk
map `𝒪_{Sp A,φ(y)} → 𝒪_{Sp B,y}` is surjective. -/
structure IsAffinoidLocallyClosedImmersion (φ : A →ₐ[K] B) : Prop where
  /-- The morphism is injective on classical points. -/
  maximalSpectrumComap_injective : Function.Injective (hB.out.maximalSpectrumComap φ)
  /-- Every stalk map is surjective. -/
  surjective_stalkMap (y : MaximalSpectrum B) : Function.Surjective (φ.stalkMap y)

/-- **Open immersions of affinoid spaces.** The morphism `Sp B → Sp A` given by `φ : A → B` is
an open immersion if it is injective on classical points and every stalk map
`𝒪_{Sp A,φ(y)} → 𝒪_{Sp B,y}` is bijective. -/
structure IsAffinoidOpenImmersion (φ : A →ₐ[K] B) : Prop where
  /-- The morphism is injective on classical points. -/
  maximalSpectrumComap_injective : Function.Injective (hB.out.maximalSpectrumComap φ)
  /-- Every stalk map is bijective. -/
  bijective_stalkMap (y : MaximalSpectrum B) : Function.Bijective (φ.stalkMap y)

/-- A locally closed immersion is a map injective on classical points with surjective stalk
maps. -/
theorem isAffinoidLocallyClosedImmersion_iff {φ : A →ₐ[K] B} :
    IsAffinoidLocallyClosedImmersion φ ↔ Function.Injective (hB.out.maximalSpectrumComap φ) ∧
      ∀ y, Function.Surjective (φ.stalkMap y) :=
  ⟨fun h ↦ ⟨h.maximalSpectrumComap_injective, h.surjective_stalkMap⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩⟩

/-- An open immersion is a map injective on classical points with bijective stalk maps. -/
theorem isAffinoidOpenImmersion_iff {φ : A →ₐ[K] B} :
    IsAffinoidOpenImmersion φ ↔ Function.Injective (hB.out.maximalSpectrumComap φ) ∧
      ∀ y, Function.Bijective (φ.stalkMap y) :=
  ⟨fun h ↦ ⟨h.maximalSpectrumComap_injective, h.bijective_stalkMap⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩⟩

/-- Open immersions are locally closed immersions. -/
theorem IsAffinoidOpenImmersion.isAffinoidLocallyClosedImmersion {φ : A →ₐ[K] B}
    (h : IsAffinoidOpenImmersion φ) : IsAffinoidLocallyClosedImmersion φ :=
  ⟨h.maximalSpectrumComap_injective, fun y ↦ (h.bijective_stalkMap y).surjective⟩

/-- **Inclusions of affinoid subdomains are open immersions.** -/
theorem IsAffinoidSubdomainMap.isAffinoidOpenImmersion {φ : A →ₐ[K] B} {U : Set (MaximalSpectrum A)}
    (hU : IsAffinoidSubdomainMap φ U) : IsAffinoidOpenImmersion φ :=
  ⟨hU.maximalSpectrumComap_injective hA.out, hU.bijective_stalkMap⟩

omit hB in
/-- The identity is an open immersion. -/
@[simp]
theorem isAffinoidOpenImmersion_id : IsAffinoidOpenImmersion (AlgHom.id K A) :=
  (IsAffinoidSubdomainMap.id hA.out).isAffinoidOpenImmersion

omit hB in
/-- The identity is a locally closed immersion. -/
@[simp]
theorem isAffinoidLocallyClosedImmersion_id : IsAffinoidLocallyClosedImmersion (AlgHom.id K A) :=
  isAffinoidOpenImmersion_id.isAffinoidLocallyClosedImmersion

/-- Locally closed immersions are closed under composition. -/
theorem IsAffinoidLocallyClosedImmersion.comp {φ : A →ₐ[K] B} {ψ : B →ₐ[K] C}
    (hφ : IsAffinoidLocallyClosedImmersion φ) (hψ : IsAffinoidLocallyClosedImmersion ψ) :
    IsAffinoidLocallyClosedImmersion (ψ.comp φ) where
  maximalSpectrumComap_injective := by
    rw [IsAffinoidAlgebra.maximalSpectrumComap_comp hB.out hC.out]
    exact hφ.maximalSpectrumComap_injective.comp hψ.maximalSpectrumComap_injective
  surjective_stalkMap z :=
    AlgHom.surjective_stalkMap_comp (hφ.surjective_stalkMap _) (hψ.surjective_stalkMap z)

/-- Open immersions are closed under composition. -/
theorem IsAffinoidOpenImmersion.comp {φ : A →ₐ[K] B} {ψ : B →ₐ[K] C}
    (hφ : IsAffinoidOpenImmersion φ) (hψ : IsAffinoidOpenImmersion ψ) :
    IsAffinoidOpenImmersion (ψ.comp φ) where
  maximalSpectrumComap_injective :=
    (hφ.isAffinoidLocallyClosedImmersion.comp
      hψ.isAffinoidLocallyClosedImmersion).maximalSpectrumComap_injective
  bijective_stalkMap z :=
    ⟨AlgHom.injective_stalkMap_comp (hφ.bijective_stalkMap _).injective
        (hψ.bijective_stalkMap z).injective,
      (hφ.isAffinoidLocallyClosedImmersion.comp
        hψ.isAffinoidLocallyClosedImmersion).surjective_stalkMap z⟩

section Finite

omit hA in
/-- If `φ : A → B` is injective on classical points, then a power of the maximal ideal of every
classical point `y` of `Sp B` lies in the extension `𝔪_{φ(y)} B`: the ideal `𝔪_{φ(y)} B` is
contained in no other maximal ideal of `B`, and `B` is a Jacobson ring. -/
private theorem exists_pow_le_map_of_injective {φ : A →ₐ[K] B}
    (hinj : Function.Injective (hB.out.maximalSpectrumComap φ)) (y : MaximalSpectrum B) :
    ∃ n : ℕ, y.asIdeal ^ n ≤ (hB.out.maximalSpectrumComap φ y).asIdeal.map φ := by
  have := hB.out.isNoetherianRing
  have := hB.out.isJacobsonRing
  refine Ideal.exists_pow_le_of_le_jacobson_of_fg (le_sInf fun P ⟨hle, hP⟩ ↦ ?_)
    (IsNoetherian.noetherian _)
  -- A maximal ideal `P ⊇ 𝔪_{φ(y)} B` lies over `𝔪_{φ(y)}`, so it is the point `y` by injectivity.
  have hPy : (⟨P, hP⟩ : MaximalSpectrum B) = y :=
    hinj (hB.out.maximalSpectrumComap_eq_of_map_le φ (P := ⟨P, hP⟩) hle)
  exact (congrArg MaximalSpectrum.asIdeal hPy).ge

/-- For a locally closed immersion `φ : A → B` and a classical point `x` of `Sp A`, every
`b ∈ B` is congruent to some `φ a` modulo `𝔪ₓ B`. -/
private theorem IsAffinoidLocallyClosedImmersion.exists_sub_mem_map {φ : A →ₐ[K] B}
    (h : IsAffinoidLocallyClosedImmersion φ) (x : MaximalSpectrum A) (b : B) :
    ∃ a : A, b - φ a ∈ x.asIdeal.map φ := by
  by_cases htop : x.asIdeal.map φ = ⊤
  · exact ⟨0, htop ▸ Submodule.mem_top⟩
  -- Otherwise a maximal ideal `y ⊇ 𝔪ₓ B` is a classical point over `x`.
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ htop
  have hy : hB.out.maximalSpectrumComap φ ⟨P, hP⟩ = x :=
    hB.out.maximalSpectrumComap_eq_of_map_le φ hle
  obtain ⟨n, hn⟩ := exists_pow_le_map_of_injective h.maximalSpectrumComap_injective ⟨P, hP⟩
  obtain ⟨a, ha⟩ := AlgHom.exists_sub_mem_pow_of_surjective_stalkMap (h.surjective_stalkMap _) n b
  exact ⟨a, hy ▸ hn ha⟩

/-- **Finite locally closed immersions are closed immersions.** If `φ : A → B` is finite and
`Sp B → Sp A` is a locally closed immersion, then `φ` is surjective. -/
theorem IsAffinoidLocallyClosedImmersion.surjective_of_finite {φ : A →ₐ[K] B}
    (h : IsAffinoidLocallyClosedImmersion φ) (hf : φ.Finite) : Function.Surjective φ := by
  let := φ.toRingHom.toAlgebra
  have : Module.Finite A B := hf
  -- By Nakayama's lemma, it suffices that `B = φ(A) + 𝔪ₓ B` for every maximal ideal `𝔪ₓ`.
  have hN := (LinearMap.range (Algebra.linearMap A B)).eq_top_of_forall_isMaximal_le_sup_smul
    fun m hm b _ ↦ by
      obtain ⟨a, ha⟩ := h.exists_sub_mem_map ⟨m, hm⟩ b
      rw [← sub_add_cancel b (algebraMap A B a)]
      refine add_mem (Submodule.mem_sup_right ?_)
        (Submodule.mem_sup_left (LinearMap.mem_range_self _ a))
      rwa [Ideal.smul_top_eq_map, RingHom.algebraMap_toAlgebra]
  intro b
  obtain ⟨a, ha⟩ := LinearMap.mem_range.mp (hN ▸ Submodule.mem_top (x := b))
  rw [Algebra.linearMap_apply, RingHom.algebraMap_toAlgebra] at ha
  exact ⟨a, ha⟩

end Finite

end TauCeti
