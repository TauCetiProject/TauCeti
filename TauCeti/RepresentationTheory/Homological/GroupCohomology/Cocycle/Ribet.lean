/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Cocycle.SelmerModule

import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import TauCeti.RepresentationTheory.Homological.GroupCohomology.Cocycle
import TauCeti.RingTheory.Ideal.ArtinRees

/-!
# Ribet cocycles

Let `G` be a group (a type with a multiplication suffices), `O` a commutative ring, `A` an
`O`-algebra acting on an `O`-module `V`, and `ρ : G → A` a map; typically `ρ : G → M_d(O)` acts on
`V = B^d` for an `O`-module `B`. Let `z : G → M` be a map to an `O`-module. A *scalar relation* of
`z` is a finitely supported `θ : G →₀ O` with `∑_g θ_g • z(g) = 0`. For a set `T ⊆ G`, the
**Ribet cocycles** `TauCeti.ribetCocycles O V z ρ T` are the `ρ`-cocycles `c : G → V`,
`c (g * h) = c g + ρ g • c h`, that vanish on `T` and obey every scalar relation of `z`: whenever
`∑_g θ_g • z(g) = 0`, also `∑_g θ_g • c(g) = 0`.

The case of interest is a finite family of representations `u_x : G → M_n(O)` and
`z(g) = (u_x(g) - 1)_x` in `∏_x M_n(O)`: the Ribet cocycles are then the cocycles that obey every
linear relation `∑_g θ_g (u_x(g) - 1) = 0` (for all `x`) among the `u_x(g) - 1`. A cocycle of the
form `g ↦ f((u_x(g) - 1)_x)` for a linear map `f`, such as one read off from the entries of the
`u_x(g)` in Ribet's method, obeys all of them. The cocycles vanishing on `T` and at `γ ∈ G` form
`TauCeti.ribetCocycles O V z ρ (insert γ T)`.

No topology is involved, so the definition makes sense for any group. For a topological `G`, the
locally constant Ribet cocycles form the Selmer module `TauCeti.cocycleSelmerModule` whose relations
are the scalar relations of `z`, read in `A` through `algebraMap O A`.

The main result is a converse up to a power of an ideal. Let `O` be noetherian, `z` a cocycle for
`σ : G → End_O(M)` with values in a finite module `M`, and `I` an ideal killing `V`. Then a Ribet
cocycle `c` is, up to `I ^ k M`, the graph of an equivariant map on a subrepresentation: there is a
submodule `Y ⊆ M × V`, stable under `(σ(g), ρ(g))` for every `g`, on which the first projection is
injective, with `(z(g) + w, c(g)) ∈ Y` for every `g` and every `w ∈ I ^ k M`. The submodule is
spanned by the pairs `(z(g), c(g))` and by `I ^ k M × 0`; it is stable because both coordinates are
cocycles. The first projection is injective on it by the Artin–Rees lemma for `I` and the span `N`
of the `z(g)`: for `k` large, an element of `N ∩ I ^ k M` is a combination `∑_g θ_g • z(g)` with all
`θ_g ∈ I`, so the corresponding combination of the `c(g)` lies in `I • V = 0`. In particular `c(g)`
depends only on `z(g)` modulo `I ^ k M`.

## Main definitions

* `TauCeti.ribetCocycles O V z ρ T`: the `ρ`-cocycles `G → V` vanishing on `T` that obey every
  scalar relation of `z`.

## Main results

* `TauCeti.mem_ribetCocycles_iff`: the defining conditions.
* `TauCeti.ribetCocycles_anti`: fewer vanishing conditions give a larger module.
* `TauCeti.comp_mem_ribetCocycles`, `TauCeti.comp_mem_ribetCocycles_iff`: a linear map of
  coefficients preserves Ribet cocycles, and an injective one reflects them.
* `TauCeti.mem_cocycleSelmerModule_iff_isLocallyConstant_and_mem_ribetCocycles`: on a topological
  group, the locally constant Ribet cocycles form a Selmer module of cocycles.
* `TauCeti.exists_forall_linearCombination_eq_zero_of_mem_pow_smul_top`: over a noetherian ring and
  for `z` in a finite module, there is `k` such that every map `c` obeying the scalar relations of
  `z`, with values killed by `I`, kills every combination `θ` with `∑_g θ_g • z(g) ∈ I ^ k M`.
* `TauCeti.exists_forall_apply_eq_apply_of_sub_mem_pow_smul_top`: in particular `c(g) = c(h)`
  whenever `z(g) - z(h) ∈ I ^ k M`.
* `TauCeti.exists_submodule_injOn_fst_of_mem_ribetCocycles`: for a cocycle `z` in a finite module
  over a noetherian ring, a Ribet cocycle with values killed by `I` lies, up to `I ^ k M`, on a
  stable submodule of `M × V` on which the first projection is injective.
* `TauCeti.exists_submodule_injOn_fst_of_mem_ribetCocycles_matrix`: the same for a finite family of
  matrix representations `u_x`, with `z(g) = (u_x(g) - 1)_x`, and a Ribet cocycle with values in
  `(O / a)^d`.

## References

* K. A. Ribet, *A modular construction of unramified p-extensions of Q(μ_p)*, Invent. Math. 34
  (1976), 151–162: cocycles read off from a residually reducible representation.
* J. Bellaïche and G. Chenevier, *Families of Galois representations and Selmer groups*,
  Astérisque 324 (2009), Chapter 1: Ribet's method for pseudocharacters and generalized matrix
  algebras.
* M. F. Atiyah and I. G. Macdonald, *Introduction to Commutative Algebra*, Addison-Wesley, 1969,
  Chapter 10 (the Artin–Rees lemma).

## Provenance

The definition follows `New.Selmer.ribetCocycles`, and the statement of
`TauCeti.exists_submodule_injOn_fst_of_mem_ribetCocycles_matrix` and the route of its proof (the
submodule spanned by the pairs `(z(g), c(g))` and the Artin–Rees lemma) follow
`New.Selmer.ribetCocycles.exists_graph_subrepresentation` (file
`src/New/Congruences/LocalLoss/Basic.lean`) in grh-lean (https://github.com/lsernau/grh-lean,
Apache 2.0, Copyright 2026 Anthropic, PBC). Here the family of matrix representations is
generalised to any cocycle with values in a finite module, the element `a` to an ideal killing the
coefficients, and the group to a type with a multiplication.
-/

public section

namespace TauCeti

section Definition

variable {G : Type*} [Mul G] (O : Type*) {A M : Type*} [CommSemiring O] [Semiring A]
  [Algebra O A] (V : Type*) [AddCommMonoid V] [Module A V] [Module O V] [IsScalarTower O A V]
  [AddCommMonoid M] [Module O M]

/-- **Ribet cocycles** relative to a map `z : G → M`: the `O`-module of the maps `c : G → V` with
`c (g * h) = c g + ρ g • c h` (`ρ`-cocycles) that vanish on `T` and obey every scalar relation of
`z`, that is `∑_g θ_g • c(g) = 0` whenever `θ : G →₀ O` has `∑_g θ_g • z(g) = 0`. For a family of
representations `u_x` and `z(g) = (u_x(g) - 1)_x`, these are the cocycles that obey every linear
relation among the `u_x(g) - 1`. -/
def ribetCocycles (z : G → M) (ρ : G → A) (T : Set G) : Submodule O (G → V) where
  carrier := {c | (∀ g h, c (g * h) = c g + ρ g • c h) ∧ (∀ g ∈ T, c g = 0) ∧
    ∀ θ : G →₀ O, Finsupp.linearCombination O z θ = 0 → Finsupp.linearCombination O c θ = 0}
  add_mem' := by
    rintro c c' ⟨hcoc, hT, hrel⟩ ⟨hcoc', hT', hrel'⟩
    refine ⟨fun g h ↦ ?_, fun g hg ↦ ?_, fun θ hθ ↦ ?_⟩
    · simp only [Pi.add_apply, hcoc, hcoc', smul_add]
      abel
    · simp [hT g hg, hT' g hg]
    · have h₁ := hrel θ hθ
      have h₂ := hrel' θ hθ
      rw [Finsupp.linearCombination_apply] at h₁ h₂ ⊢
      simp only [Pi.add_apply, smul_add, Finsupp.sum_add, h₁, h₂, add_zero]
  zero_mem' := ⟨by simp, by simp, fun θ _ ↦ by simp⟩
  smul_mem' := by
    rintro r c ⟨hcoc, hT, hrel⟩
    refine ⟨fun g h ↦ ?_, fun g hg ↦ ?_, fun θ hθ ↦ ?_⟩
    · simp only [Pi.smul_apply, hcoc, smul_add, smul_comm r (ρ g)]
    · simp [hT g hg]
    · have h := hrel θ hθ
      rw [Finsupp.linearCombination_apply] at h ⊢
      simp only [Pi.smul_apply, smul_comm _ r, ← Finsupp.smul_sum, h, smul_zero]

variable {O V} {z : G → M} {ρ : G → A} {T : Set G} {c : G → V}

/-- Membership in the Ribet cocycles: `c` is a `ρ`-cocycle vanishing on `T` and obeying every
scalar relation of `z`. -/
@[simp]
theorem mem_ribetCocycles_iff :
    c ∈ ribetCocycles O V z ρ T ↔ (∀ g h, c (g * h) = c g + ρ g • c h) ∧ (∀ g ∈ T, c g = 0) ∧
      ∀ θ : G →₀ O, Finsupp.linearCombination O z θ = 0 → Finsupp.linearCombination O c θ = 0 :=
  Iff.rfl

/-- A Ribet cocycle is a `ρ`-cocycle. -/
theorem apply_mul_of_mem_ribetCocycles (hc : c ∈ ribetCocycles O V z ρ T) (g h : G) :
    c (g * h) = c g + ρ g • c h :=
  hc.1 g h

/-- A Ribet cocycle vanishes on `T`. -/
theorem apply_eq_zero_of_mem_ribetCocycles (hc : c ∈ ribetCocycles O V z ρ T) {g : G}
    (hg : g ∈ T) : c g = 0 :=
  hc.2.1 g hg

/-- A Ribet cocycle obeys every scalar relation of `z`. -/
theorem linearCombination_eq_zero_of_mem_ribetCocycles (hc : c ∈ ribetCocycles O V z ρ T)
    {θ : G →₀ O} (hθ : Finsupp.linearCombination O z θ = 0) :
    Finsupp.linearCombination O c θ = 0 :=
  hc.2.2 θ hθ

/-- **The Ribet cocycles are antitone in the vanishing set**: dropping vanishing conditions gives a
larger module. -/
theorem ribetCocycles_anti {T' : Set G} (hT : T' ⊆ T) :
    ribetCocycles O V z ρ T ≤ ribetCocycles O V z ρ T' :=
  fun _ ⟨hcoc, hT₀, hrel⟩ ↦ ⟨hcoc, fun g hg ↦ hT₀ g (hT hg), hrel⟩

section Map

variable {W : Type*} [AddCommMonoid W] [Module A W] [Module O W] [IsScalarTower O A W]
  {f : V →ₗ[A] W}

/-- **Composition with an `A`-linear map of coefficients preserves Ribet cocycles.** -/
theorem comp_mem_ribetCocycles (hc : c ∈ ribetCocycles O V z ρ T) :
    f ∘ c ∈ ribetCocycles O W z ρ T := by
  obtain ⟨hcoc, hT, hrel⟩ := hc
  refine ⟨fun g h ↦ by simp [hcoc], fun g hg ↦ by simp [hT g hg], fun θ hθ ↦ ?_⟩
  have h := Finsupp.apply_linearCombination O (f.restrictScalars O) c θ
  rw [hrel θ hθ, map_zero] at h
  simpa using h.symm

/-- **An injective map of coefficients preserves and reflects Ribet cocycles**: for `f`
injective, `f ∘ c` is a Ribet cocycle exactly when `c` is. -/
theorem comp_mem_ribetCocycles_iff (hf : Function.Injective f) :
    f ∘ c ∈ ribetCocycles O W z ρ T ↔ c ∈ ribetCocycles O V z ρ T := by
  refine ⟨fun ⟨hcoc, hT, hrel⟩ ↦ ⟨fun g h ↦ hf ?_, fun g hg ↦ hf ?_, fun θ hθ ↦ hf ?_⟩,
    comp_mem_ribetCocycles⟩
  · simpa using hcoc g h
  · simpa using hT g hg
  · have h := Finsupp.apply_linearCombination O (f.restrictScalars O) c θ
    simp only [LinearMap.coe_restrictScalars] at h
    rw [h, hrel θ hθ, map_zero]

end Map

/-- **Locally constant Ribet cocycles are a Selmer module.** On a topological `G`, the Selmer module
of cocycles vanishing on `T` whose relations are the scalar relations of `z`, read in `A` through
`algebraMap O A`, consists of the locally constant Ribet cocycles. -/
theorem mem_cocycleSelmerModule_iff_isLocallyConstant_and_mem_ribetCocycles [TopologicalSpace G] :
    c ∈ cocycleSelmerModule O V ρ T (Finsupp.mapRange.linearMap (Algebra.linearMap O A) ''
        LinearMap.ker (Finsupp.linearCombination O z)) ↔
      IsLocallyConstant c ∧ c ∈ ribetCocycles O V z ρ T := by
  have h (θ : G →₀ O) : Finsupp.linearCombination A c
      (Finsupp.mapRange.linearMap (Algebra.linearMap O A) θ) =
        Finsupp.linearCombination O c θ := by
    simp [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index, algebraMap_smul]
  simp only [mem_cocycleSelmerModule_iff, mem_ribetCocycles_iff, Set.forall_mem_image,
    SetLike.mem_coe, LinearMap.mem_ker, h]

end Definition

section ArtinRees

variable {G : Type*} {O : Type*} [CommRing O] [IsNoetherianRing O] {M V : Type*}
  [AddCommGroup V] [Module O V] [AddCommGroup M] [Module O M] [Module.Finite O M]

/-- **Combinations deep in the `I`-adic filtration vanish for maps obeying the scalar relations.**
Over a noetherian ring, for `z` with values in a finite module `M` and an ideal `I` killing `V`,
there is `k` such that every `c : G → V` obeying the scalar relations of `z` has
`∑_g θ_g • c(g) = 0` whenever `∑_g θ_g • z(g) ∈ I ^ k M`. The same `k` serves every such `c`. -/
theorem exists_forall_linearCombination_eq_zero_of_mem_pow_smul_top {z : G → M} {I : Ideal O}
    (hV : Module.IsTorsionBySet O V I) :
    ∃ k : ℕ, ∀ c : G → V,
      (∀ θ : G →₀ O, Finsupp.linearCombination O z θ = 0 → Finsupp.linearCombination O c θ = 0) →
        ∀ θ : G →₀ O, Finsupp.linearCombination O z θ ∈ I ^ k • (⊤ : Submodule O M) →
          Finsupp.linearCombination O c θ = 0 := by
  -- Artin–Rees for the span of the `z(g)`, which is the range of `θ ↦ ∑_g θ_g • z(g)`.
  obtain ⟨k, hk⟩ := ArtinRees.exists_controlled_lift I
    (LinearMap.range (Finsupp.linearCombination O z))
  refine ⟨1 + k, fun c hrel θ hθ ↦ ?_⟩
  -- The combination `∑_g θ_g • z(g)` is also `∑_g θ'_g • z(g)` with `θ' ∈ I • ⊤`.
  obtain ⟨θ', hθ', hθ'θ⟩ := hk (Finsupp.linearCombination O z).rangeRestrict
    (LinearMap.surjective_rangeRestrict _) 1 ⟨_, LinearMap.mem_range_self _ θ⟩ hθ
  have hzθ : Finsupp.linearCombination O z (θ - θ') = 0 := by
    rw [map_sub, sub_eq_zero]
    exact (congrArg Subtype.val hθ'θ).symm
  have hcθ := hrel (θ - θ') hzθ
  rw [map_sub, sub_eq_zero] at hcθ
  -- So `∑_g θ_g • c(g) = ∑_g θ'_g • c(g)` lies in `I • V = 0`.
  have h := Submodule.smul_top_le_comap_smul_top _ (Finsupp.linearCombination O c) hθ'
  rw [pow_one, Submodule.mem_comap, ← hcθ] at h
  exact (Submodule.mem_bot O).mp
    ((Submodule.smul_le.mpr fun r hr v _ ↦ (Submodule.mem_bot O).mpr (@hV v ⟨r, hr⟩)) h)

/-- **A map obeying the scalar relations of `z` depends only on `z` modulo a power of the ideal.**
Over a noetherian ring, for `z` with values in a finite module `M` and an ideal `I` killing `V`,
there is `k` such that every `c : G → V` obeying the scalar relations of `z` has `c(g) = c(h)`
whenever `z(g) - z(h) ∈ I ^ k M`. -/
theorem exists_forall_apply_eq_apply_of_sub_mem_pow_smul_top {z : G → M} {I : Ideal O}
    (hV : Module.IsTorsionBySet O V I) :
    ∃ k : ℕ, ∀ c : G → V,
      (∀ θ : G →₀ O, Finsupp.linearCombination O z θ = 0 → Finsupp.linearCombination O c θ = 0) →
        ∀ g h, z g - z h ∈ I ^ k • (⊤ : Submodule O M) → c g = c h := by
  obtain ⟨k, hk⟩ := exists_forall_linearCombination_eq_zero_of_mem_pow_smul_top (z := z) hV
  refine ⟨k, fun c hrel g h hgh ↦ ?_⟩
  have := hk c hrel (Finsupp.single g 1 - Finsupp.single h 1) (by simpa using hgh)
  simpa [sub_eq_zero] using this

end ArtinRees

section Graph

variable {G : Type*} [Mul G] {O : Type*} [CommRing O] [IsNoetherianRing O] {A M V : Type*}
  [Semiring A] [Algebra O A] [AddCommGroup V] [Module A V] [Module O V] [IsScalarTower O A V]
  [AddCommGroup M] [Module O M] [Module.Finite O M]

/-- **Ribet cocycles are graphs up to a power of the ideal.** Let `O` be noetherian, `z : G → M` a
cocycle for `σ : G → End_O(M)` with values in a finite `O`-module, and `c` a Ribet cocycle relative
to `z` (for `ρ : G → A`) whose values are killed by an ideal `I`. Then there are `k` and a submodule
`Y ⊆ M × V`, stable under `(m, v) ↦ (σ(g) m, ρ(g) • v)` for every `g`, on which the first
projection is injective, with `(z(g) + w, c(g)) ∈ Y` for every `g` and every `w ∈ I ^ k M`. So, on
the first projection of `Y`, which contains every `z(g) + w`, there is an `O`-linear map whose graph
is `Y`; it intertwines `σ` and `ρ` and sends `z(g) + w` to `c(g)`. -/
theorem exists_submodule_injOn_fst_of_mem_ribetCocycles {σ : G → Module.End O M} {z : G → M}
    (hz : ∀ g h, z (g * h) = z g + σ g (z h)) {ρ : G → A} {T : Set G} {c : G → V}
    (hc : c ∈ ribetCocycles O V z ρ T) {I : Ideal O} (hV : Module.IsTorsionBySet O V I) :
    ∃ k : ℕ, ∃ Y : Submodule O (M × V), (∀ g, ∀ y ∈ Y, (σ g y.1, ρ g • y.2) ∈ Y) ∧
      Set.InjOn Prod.fst (Y : Set (M × V)) ∧
        ∀ g, ∀ w ∈ I ^ k • (⊤ : Submodule O M), (z g + w, c g) ∈ Y := by
  obtain ⟨k, hk⟩ := exists_forall_linearCombination_eq_zero_of_mem_pow_smul_top (z := z) hV
  have hpair (θ : G →₀ O) : Finsupp.linearCombination O (fun g ↦ (z g, c g)) θ =
      (Finsupp.linearCombination O z θ, Finsupp.linearCombination O c θ) := by
    induction θ using Finsupp.induction_linear with
    | zero => simp only [map_zero, Prod.mk_zero_zero]
    | add θ₁ θ₂ h₁ h₂ => simp only [map_add, h₁, h₂, Prod.mk_add_mk]
    | single g r => simp
  -- `Y` is spanned by the pairs `(z(g), c(g))` and by `I ^ k M × 0`.
  let W : Submodule O M := I ^ k • ⊤
  refine ⟨k, Submodule.span O (Set.range fun g ↦ (z g, c g)) ⊔ W.prod ⊥, fun g y hy ↦ ?_, ?_,
    fun g w hw ↦ ?_⟩
  · -- Stability: the pairs form a cocycle for `(σ(g), ρ(g))`, so their span is stable, and
    -- `W × 0` is stable.
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨hq₁, hq₂⟩ := Submodule.mem_prod.mp hq
    rw [Submodule.mem_bot] at hq₂
    let τ (g : G) : Module.End O (M × V) := (σ g).prodMap (DistribSMul.toLinearMap O V (ρ g))
    have hτ (g h : G) : (z (g * h), c (g * h)) = (z g, c g) + τ g (z h, c h) := by
      simp [τ, hz, apply_mul_of_mem_ribetCocycles hc]
    have hsplit : (σ g (p + q).1, ρ g • (p + q).2) = τ g p + (σ g q.1, 0) := by
      simp [τ, hq₂]
    rw [hsplit]
    exact Submodule.add_mem_sup (apply_mem_span_range_of_cocycle (z := fun g ↦ (z g, c g)) hτ g hp)
      (Submodule.mem_prod.mpr ⟨Submodule.smul_top_le_comap_smul_top _ (σ g) hq₁, zero_mem _⟩)
  · -- Injectivity: if `∑_g θ_g • z(g) + w = 0` with `w ∈ I ^ k M`, then `∑_g θ_g • c(g) = 0`.
    suffices h : ∀ y ∈ Submodule.span O (Set.range fun g ↦ (z g, c g)) ⊔ W.prod ⊥,
        y.1 = 0 → y.2 = 0 by
      intro y₁ h₁ y₂ h₂ heq
      exact Prod.ext heq (sub_eq_zero.mp (h _ (Submodule.sub_mem _ h₁ h₂) (by simp [heq])))
    intro y hy hy₁
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨hq₁, hq₂⟩ := Submodule.mem_prod.mp hq
    rw [Submodule.mem_bot] at hq₂
    rw [← Finsupp.range_linearCombination] at hp
    obtain ⟨θ, rfl⟩ := hp
    rw [hpair] at hy₁ ⊢
    have hθ : Finsupp.linearCombination O z θ = -q.1 := eq_neg_of_add_eq_zero_left hy₁
    simp [hq₂, hk c hc.2.2 θ (hθ ▸ Submodule.neg_mem _ hq₁)]
  · -- Membership: `(z(g) + w, c(g)) = (z(g), c(g)) + (w, 0)`.
    have h : (z g + w, c g) = (z g, c g) + (w, 0) := by simp
    rw [h]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨g, rfl⟩)
      (Submodule.mem_prod.mpr ⟨hw, zero_mem _⟩)

end Graph

section Matrix

open scoped Matrix.Module

variable {G X O : Type*} [Mul G] [Finite X] [CommRing O] [IsNoetherianRing O] {n d : Type*}
  [Fintype n] [DecidableEq n] [Fintype d] [DecidableEq d]

/-- **Ribet cocycles of a family of matrix representations are graphs up to `a ^ k`.** Let `O` be
noetherian, `a ∈ O`, `X` finite, `u_x : G → M_n(O)` (`x ∈ X`) multiplicative maps, `ρ : G → M_d(O)`
any map, and `c : G → (O / a)^d` a Ribet cocycle of `ρ` relative to the family `(u_x(g) - 1)_x`.
Then there are `k` and a submodule `Y` of `(∏_x M_n(O)) × (O / a)^d`, stable under left
multiplication by `(u_x(g))_x` on the first factor and by `ρ(g)` on the second, on which the first
projection is injective, such that `((u_x(g) - 1)_x + a ^ k v, c(g)) ∈ Y` for every `g ∈ G` and
every `v ∈ ∏_x M_n(O)`. -/
theorem exists_submodule_injOn_fst_of_mem_ribetCocycles_matrix {u : X → G → Matrix n n O}
    (hu : ∀ x g h, u x (g * h) = u x g * u x h) {ρ : G → Matrix d d O} {T : Set G} {a : O}
    {c : G → d → O ⧸ Ideal.span {a}}
    (hc : c ∈ ribetCocycles O (d → O ⧸ Ideal.span {a}) (fun g x ↦ u x g - 1) ρ T) :
    ∃ k : ℕ, ∃ Y : Submodule O ((X → Matrix n n O) × (d → O ⧸ Ideal.span {a})),
      (∀ g, ∀ y ∈ Y, (fun x ↦ u x g * y.1 x, ρ g • y.2) ∈ Y) ∧
      Set.InjOn Prod.fst (Y : Set ((X → Matrix n n O) × (d → O ⧸ Ideal.span {a}))) ∧
        ∀ g (v : X → Matrix n n O), ((fun x ↦ u x g - 1) + a ^ k • v, c g) ∈ Y := by
  -- The family `g ↦ (u_x(g) - 1)_x` is a cocycle for left multiplication by `(u_x(g))_x`.
  have hz : ∀ g h, (fun x ↦ u x (g * h) - 1) =
      (fun x ↦ u x g - 1) + LinearMap.mulLeft O (fun x ↦ u x g) (fun x ↦ u x h - 1) := by
    intro g h
    funext x
    simp [hu, mul_sub]
  have hq : Module.IsTorsionBySet O (O ⧸ Ideal.span {a}) (Ideal.span {a}) :=
    (Module.isTorsionBySet_quotient_iff _ _).mpr fun x _ hr ↦ Ideal.mul_mem_right x _ hr
  have hV : Module.IsTorsionBySet O (d → O ⧸ Ideal.span {a}) (Ideal.span {a}) :=
    fun v r ↦ funext fun i ↦ @hq (v i) r
  obtain ⟨k, Y, hstable, hinj, hmem⟩ := exists_submodule_injOn_fst_of_mem_ribetCocycles hz hc hV
  refine ⟨k, Y, fun g y hy ↦ ?_, hinj, fun g v ↦ hmem g _ ?_⟩
  · simpa [Pi.mul_def] using hstable g y hy
  · exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self a) k)
      Submodule.mem_top

end Matrix

end TauCeti
