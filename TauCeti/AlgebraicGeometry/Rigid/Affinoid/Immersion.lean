/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Rigid.Affinoid.StalkMap

import Mathlib.RingTheory.Finiteness.Nakayama
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Locally closed and open immersions of affinoid spaces

A `K`-algebra map `φ : A → B` of affinoid algebras is a morphism `Sp B → Sp A`. It is a
*locally closed immersion* (`TauCeti.IsLocallyClosedImmersion`) if it is injective on classical
points and every stalk map `φ*_y : 𝒪_{Sp A,φ(y)} → 𝒪_{Sp B,y}` is surjective, and an *open
immersion* (`TauCeti.IsOpenImmersion`) if it is injective on classical points and every stalk map is
bijective. Like affinoid subdomains and Runge immersions, both notions are algebraic: no norm on
`A` or `B` is chosen.

The inclusion of an affinoid subdomain is an open immersion, since it induces isomorphisms of
stalks; in particular the identity is one. Open immersions are locally closed immersions, and both
classes are closed under composition. A locally closed immersion whose algebra map `φ` is finite
is a closed immersion, that is, `φ` is surjective: for a maximal ideal `𝔪ₓ` of `A`, the ideal
`𝔪ₓ B` lies in no prime ideal other than the maximal ideal of the unique point `y` over `x` (if
there is one), so it contains a power `𝔪_yⁿ`, and surjectivity of the stalk map at `y` gives
`B = φ(A) + 𝔪_yⁿ ⊆ φ(A) + 𝔪ₓ B`. Nakayama's lemma, applied at every maximal ideal to the finite
`A`-module `B ⧸ φ(A)`, shows that it vanishes.

Injectivity on points is not implied by the stalk condition: the diagonal `K → K × K` has
bijective stalk maps at both points of `Sp (K × K)` but maps them to the single point of `Sp K`.
Surjectivity of the stalk maps is not implied by injectivity on points either: the normalisation
`K⟨X, Y⟩ ⧸ (Y² - X³) → K⟨t⟩` of the cusp, `X ↦ t²`, `Y ↦ t³`, is injective on classical points,
but its stalk map at the origin misses `t`.

## Main definitions

* `TauCeti.IsLocallyClosedImmersion φ`: `Sp B → Sp A` is a locally closed immersion.
* `TauCeti.IsOpenImmersion φ`: `Sp B → Sp A` is an open immersion.

## Main results

* `TauCeti.IsAffinoidSubdomainMap.isOpenImmersion`: inclusions of affinoid subdomains are open
  immersions.
* `TauCeti.IsOpenImmersion.isLocallyClosedImmersion`: open immersions are locally closed.
* `TauCeti.IsLocallyClosedImmersion.comp`, `TauCeti.IsOpenImmersion.comp`: both classes are
  closed under composition.
* `TauCeti.IsLocallyClosedImmersion.surjective_of_finite`: a finite locally closed immersion is a
  closed immersion.

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
structure IsLocallyClosedImmersion (φ : A →ₐ[K] B) : Prop where
  /-- The morphism is injective on classical points. -/
  injective : Function.Injective (hB.out.maximalSpectrumComap φ)
  /-- Every stalk map is surjective. -/
  surjective_stalkMap (y : MaximalSpectrum B) : Function.Surjective (φ.stalkMap y)

/-- **Open immersions of affinoid spaces.** The morphism `Sp B → Sp A` given by `φ : A → B` is
an open immersion if it is injective on classical points and every stalk map
`𝒪_{Sp A,φ(y)} → 𝒪_{Sp B,y}` is bijective. -/
structure IsOpenImmersion (φ : A →ₐ[K] B) : Prop where
  /-- The morphism is injective on classical points. -/
  injective : Function.Injective (hB.out.maximalSpectrumComap φ)
  /-- Every stalk map is bijective. -/
  bijective_stalkMap (y : MaximalSpectrum B) : Function.Bijective (φ.stalkMap y)

/-- Open immersions are locally closed immersions. -/
theorem IsOpenImmersion.isLocallyClosedImmersion {φ : A →ₐ[K] B} (h : IsOpenImmersion φ) :
    IsLocallyClosedImmersion φ :=
  ⟨h.injective, fun y ↦ (h.bijective_stalkMap y).surjective⟩

/-- **Inclusions of affinoid subdomains are open immersions.** -/
theorem IsAffinoidSubdomainMap.isOpenImmersion {φ : A →ₐ[K] B} {U : Set (MaximalSpectrum A)}
    (hU : IsAffinoidSubdomainMap φ U) : IsOpenImmersion φ :=
  ⟨hU.maximalSpectrumComap_injective hA.out, hU.bijective_stalkMap⟩

omit hB in
/-- The identity is an open immersion. -/
theorem isOpenImmersion_id : IsOpenImmersion (AlgHom.id K A) :=
  (IsAffinoidSubdomainMap.id hA.out).isOpenImmersion

/-- Locally closed immersions are closed under composition. -/
theorem IsLocallyClosedImmersion.comp {φ : A →ₐ[K] B} {ψ : B →ₐ[K] C}
    (hφ : IsLocallyClosedImmersion φ) (hψ : IsLocallyClosedImmersion ψ) :
    IsLocallyClosedImmersion (ψ.comp φ) where
  injective := by
    rw [IsAffinoidAlgebra.maximalSpectrumComap_comp hB.out hC.out]
    exact hφ.injective.comp hψ.injective
  surjective_stalkMap z :=
    AlgHom.surjective_stalkMap_comp (hφ.surjective_stalkMap _) (hψ.surjective_stalkMap z)

/-- Open immersions are closed under composition. -/
theorem IsOpenImmersion.comp {φ : A →ₐ[K] B} {ψ : B →ₐ[K] C}
    (hφ : IsOpenImmersion φ) (hψ : IsOpenImmersion ψ) :
    IsOpenImmersion (ψ.comp φ) where
  injective := (hφ.isLocallyClosedImmersion.comp hψ.isLocallyClosedImmersion).injective
  bijective_stalkMap z :=
    ⟨AlgHom.injective_stalkMap_comp (hφ.bijective_stalkMap _).injective
        (hψ.bijective_stalkMap z).injective,
      (hφ.isLocallyClosedImmersion.comp hψ.isLocallyClosedImmersion).surjective_stalkMap z⟩

section Finite

omit hA in
/-- If `φ : A → B` is finite and injective on classical points, then a power of the maximal ideal
of every classical point `y` of `Sp B` lies in the extension `𝔪_{φ(y)} B`: the ideal `𝔪_{φ(y)} B`
is contained in no other prime ideal of `B`. -/
private theorem exists_pow_le_map_of_injective {φ : A →ₐ[K] B}
    (hinj : Function.Injective (hB.out.maximalSpectrumComap φ)) (hf : φ.Finite)
    (y : MaximalSpectrum B) :
    ∃ n : ℕ, y.asIdeal ^ n ≤ (hB.out.maximalSpectrumComap φ y).asIdeal.map φ := by
  have := hB.out.isNoetherianRing
  refine Ideal.exists_pow_le_of_le_radical_of_fg ?_ (IsNoetherian.noetherian _)
  rw [Ideal.radical_eq_sInf]
  refine le_sInf fun P ⟨hle, hP⟩ ↦ ?_
  -- A prime `P ⊇ 𝔪_{φ(y)} B` lies over the maximal ideal `𝔪_{φ(y)}`, so it is maximal, and it is
  -- the point `y` by injectivity.
  have hPx : P.comap φ.toRingHom = (hB.out.maximalSpectrumComap φ y).asIdeal :=
    ((MaximalSpectrum.isMaximal _).eq_of_le (Ideal.IsPrime.comap _).ne_top
      (Ideal.map_le_iff_le_comap.mp hle)).symm
  have hPmax : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap φ.toRingHom
    hf.to_isIntegral P (hPx ▸ MaximalSpectrum.isMaximal _)
  have hPy : (⟨P, hPmax⟩ : MaximalSpectrum B) = y :=
    hinj (MaximalSpectrum.ext ((IsAffinoidAlgebra.maximalSpectrumComap_asIdeal _ _ _).trans hPx))
  exact (congrArg MaximalSpectrum.asIdeal hPy).ge

/-- For a finite locally closed immersion `φ : A → B` and a classical point `x` of `Sp A`, every
`b ∈ B` is congruent to some `φ a` modulo `𝔪ₓ B`. -/
private theorem IsLocallyClosedImmersion.exists_sub_mem_map {φ : A →ₐ[K] B}
    (h : IsLocallyClosedImmersion φ) (hf : φ.Finite) (x : MaximalSpectrum A) (b : B) :
    ∃ a : A, b - φ a ∈ x.asIdeal.map φ := by
  by_cases htop : x.asIdeal.map φ = ⊤
  · exact ⟨0, htop ▸ Submodule.mem_top⟩
  -- Otherwise a maximal ideal `y ⊇ 𝔪ₓ B` is a classical point over `x`.
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ htop
  have hy : hB.out.maximalSpectrumComap φ ⟨P, hP⟩ = x := MaximalSpectrum.ext
    ((IsAffinoidAlgebra.maximalSpectrumComap_asIdeal _ _ _).trans
      (x.isMaximal.eq_of_le (Ideal.IsPrime.comap _).ne_top (Ideal.map_le_iff_le_comap.mp hle)).symm)
  obtain ⟨n, hn⟩ := exists_pow_le_map_of_injective h.injective hf ⟨P, hP⟩
  obtain ⟨a, ha⟩ := AlgHom.exists_sub_mem_pow_of_surjective_stalkMap (h.surjective_stalkMap _) n b
  exact ⟨a, hy ▸ hn ha⟩

/-- **Finite locally closed immersions are closed immersions.** If `φ : A → B` is finite and
`Sp B → Sp A` is a locally closed immersion, then `φ` is surjective. -/
theorem IsLocallyClosedImmersion.surjective_of_finite {φ : A →ₐ[K] B}
    (h : IsLocallyClosedImmersion φ) (hf : φ.Finite) : Function.Surjective φ := by
  let := φ.toRingHom.toAlgebra
  have : Module.Finite A B := hf
  let N : Submodule A B := LinearMap.range (Algebra.linearMap A B)
  -- By Nakayama's lemma at every maximal ideal `𝔪ₓ`, the annihilator of the finite module
  -- `B ⧸ φ(A)` lies in no maximal ideal.
  have hann : Module.annihilator A (B ⧸ N) = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    have hsmul : (⊤ : Submodule A (B ⧸ N)) ≤ m • ⊤ := by
      rintro q -
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective N q
      obtain ⟨a, ha⟩ := h.exists_sub_mem_map hf ⟨m, hm⟩ b
      have hq : Submodule.Quotient.mk (p := N) b =
          Submodule.Quotient.mk (b - algebraMap A B a) := by
        rw [Submodule.Quotient.eq, sub_sub_cancel]
        exact ⟨a, rfl⟩
      have hmem : b - algebraMap A B a ∈ m • (⊤ : Submodule A B) := by
        rw [Ideal.smul_top_eq_map]
        exact ha
      rw [hq]
      have hmap := Submodule.mem_map_of_mem (f := N.mkQ) hmem
      rwa [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at hmap
    obtain ⟨r, hr, hrN⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m ⊤
      (Module.Finite.fg_top (R := A) (M := B ⧸ N)) hsmul
    refine hm.ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
    simpa using sub_mem (hle (Module.mem_annihilator.mpr fun q ↦ hrN q trivial)) hr
  intro b
  have hb : Submodule.Quotient.mk (p := N) b = 0 := by
    simpa using Module.mem_annihilator.mp (hann ▸ Submodule.mem_top : (1 : A) ∈ _)
      (Submodule.Quotient.mk b)
  obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero N).mp hb
  exact ⟨a, ha⟩

end Finite

end TauCeti
