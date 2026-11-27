/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Matrix.Module
public import Mathlib.RingTheory.Length
public import Mathlib.Topology.LocallyConstant.Basic
public import TauCeti.RingTheory.DiscreteValuationRing.MatlisDual

/-!
# Selmer modules of cocycles

Let `G` be a topological group (a topological space with a multiplication suffices), `O` a
commutative ring, `A` an `O`-algebra and `ρ : G → A` a map, typically a matrix representation
`G → Mₙ(O)`. For an `A`-module `V`, a `ρ`-cocycle is a map
`c : G → V` with `c (g * h) = c g + ρ g • c h`. A *relation* is a finitely supported function
`R : G →₀ A`, and `c` *obeys* `R` when `∑_g R(g) • c(g) = 0`, that is when Mathlib's
`Finsupp.linearCombination A c R` vanishes. For a set `X ⊆ G` and a set `L` of relations, the
**Selmer module** `Sel(ρ, X, L; V)` (`TauCeti.cocycleSelmerModule O V ρ X L`) is the `O`-module of
the locally constant `ρ`-cocycles `c : G → V` that vanish on `X` and obey every relation of `L`.
The cocycle identity is Mathlib's `groupCohomology.IsCocycle₁` for `G` acting on `V` through `ρ`;
that action is not an instance here, since `ρ` is an arbitrary map and the coefficients `V` vary
while `ρ` and the relations stay fixed.

In the arithmetic application `G = Gal(Ω/E)` for a number field `E` inside a field `Ω`,
`ρ : G → Mₙ(O)`, `V = Bⁿ` for an `O`-module `B`, with `Mₙ(O)` acting on `Bⁿ` by Mathlib's
`Matrix.Module.matrixModule`, and `X` is the union of the inertia groups at the places of `Ω` above
the finite places of `E` outside a set `S` (`TauCeti.GaloisRep.inertiaAbove`): the members are the
locally constant cocycles unramified outside `S`. The relations carry the remaining local
conditions, for instance `c(γ) = 0` at a single element, or linear conditions on the restriction
of `c` to a decomposition group. The ring `O` and the relations are fixed while the coefficients
`B` vary, typically between `O/a` and `K/O` for the fraction field `K` of `O`.

This is a module of cocycles, not of cohomology classes. A relation such as `c(γ) = 0` is not
invariant under adding coboundaries, so the module is not the Selmer group of a Selmer structure
on `H¹` (`TauCeti.ContCohomology.SelmerStructure`), whose local conditions are subgroups of local
cohomology groups. In the module-theoretic language of `TauCeti.SelmerData` it is the Selmer
module on the module of locally constant `ρ`-cocycles, with the evaluations at the elements of
`X` and the maps `c ↦ ∑_g R(g) • c(g)` for `R ∈ L` as localisation maps to `V`, and zero local
conditions. Classes and cocycles meet in the vanishing conditions: where `ρ` is trivial on a
subgroup `I`, a cocycle vanishing on `I` is the cocycle form of the unramified local condition at
`I` (`TauCeti/RepresentationTheory/Homological/ContCohomology/Unramified.lean`).

Every defining condition is a condition on the values of `c`, so an injective `A`-linear map
`f : V → W` of coefficients preserves and reflects membership
(`TauCeti.comp_mem_cocycleSelmerModule_iff`). If moreover `f` maps onto the `a`-torsion of `W`,
composition with `f` identifies `Sel(ρ, X, L; V)` with the `a`-torsion of `Sel(ρ, X, L; W)`. For a
domain `O` with fraction field `K` and `a ≠ 0`, division by `a` embeds `O/a` onto the `a`-torsion of
`K/O`, so the Selmer module with coefficients `(O/a)ⁿ` has the length of the `a`-torsion of the
one with coefficients `(K/O)ⁿ`, and at most the length of the latter, the *divisible Selmer
length*.

## Main definitions

* `TauCeti.cocycleSelmerModule O V ρ X L`: the Selmer module of cocycles.
* `TauCeti.cocycleSelmerModuleMap O ρ X L f`: composition with an `A`-linear map `f : V → W` of
  coefficients.

## Main results

* `TauCeti.mem_cocycleSelmerModule_iff`: the defining conditions.
* `TauCeti.cocycleSelmerModule_anti`: fewer vanishing conditions and fewer relations give a larger
  module.
* `TauCeti.smul_sub_mem_cocycleSelmerModule`: for multiplicative `ρ`, the coboundaries
  `g ↦ ρ g • v - v` are cocycles.
* `TauCeti.comp_mem_cocycleSelmerModule_iff`, `TauCeti.cocycleSelmerModule_eq_comap`: an injective
  map of coefficients preserves and reflects membership.
* `TauCeti.range_cocycleSelmerModuleMap`: for `f` injective onto the `a`-torsion of `W`,
  composition with `f` maps `Sel(ρ, X, L; V)` onto the `a`-torsion of `Sel(ρ, X, L; W)`.
* `TauCeti.length_cocycleSelmerModule_eq_length_torsionBy` and
  `TauCeti.length_cocycleSelmerModule_le_of_injective`: the corresponding statements on lengths.
* `TauCeti.range_cocycleSelmerModuleMap_mapMatrixModule`: for `ρ : G → Mₙ(O)` and `f : M → N`
  injective onto the `a`-torsion of `N`, such as `O/a → B`, composition with `f` in each
  coordinate maps `Sel(ρ, X, L; Mⁿ)` onto the `a`-torsion of `Sel(ρ, X, L; Nⁿ)`.
* `TauCeti.length_cocycleSelmerModule_quotient_eq_length_torsionBy` and
  `TauCeti.length_cocycleSelmerModule_quotient_le`: for `ρ : G → Mₙ(O)` over a domain `O` with
  fraction field `K` and `a ≠ 0`, the length with coefficients `(O/a)ⁿ` is that of the `a`-torsion
  with coefficients `(K/O)ⁿ`, and at most the length with coefficients `(K/O)ⁿ`.

## References

* K. Rubin, *Euler Systems*, Annals of Mathematics Studies 147, Princeton University Press,
  2000, Chapter 1: the comparison of `H¹` with coefficients `W[a]` and the `a`-torsion of
  `H¹` with coefficients `W`, of which the comparison here is the cocycle form.

## Provenance

The definition and the comparison of torsion and divisible coefficients follow the statements of
`New.selmerModule` (`src/Lib/GaloisRep/Main/SelmerModules.lean`) and
`New.Selmer.range_selmerModuleMapOfInjective`, `New.Selmer.length_selmerModule_le_divisibleQuot`
(`src/Lib/GaloisRep/Main/DivisibleSelmerModules.lean`) in grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), which concern
`Gal(Ω/E)`, matrix representations and a discrete valuation ring `O`. **Adapted, not copied**:
here `ρ` takes values in any `O`-algebra acting on the coefficients, `G` is any topological space
with a multiplication and the vanishing conditions are on an arbitrary subset of it, and the
comparison is stated for any injective map onto the `a`-torsion, and for `O/a → K/O` over any
domain `O`.
-/

public section

open Function Submodule

namespace TauCeti

section Definition

variable {G : Type*} [Mul G] [TopologicalSpace G] (O : Type*) {A : Type*} [CommSemiring O]
  [Semiring A] [Algebra O A] (V : Type*) [AddCommMonoid V] [Module A V] [Module O V]
  [IsScalarTower O A V]

/-- **The Selmer module of cocycles** `Sel(ρ, X, L; V)`: the `O`-module of locally constant maps
`c : G → V` with `c (g * h) = c g + ρ g • c h` (`ρ`-cocycles) that vanish on `X` and obey every
relation `R ∈ L`, that is `∑_g R(g) • c(g) = 0`. For `G = Gal(Ω/E)`, `V = Bⁿ` and `X` the union
of the inertia groups above the places outside a set `S` (`TauCeti.GaloisRep.inertiaAbove`), it is
the Selmer module of the cocycles unramified outside `S` obeying `L`. -/
def cocycleSelmerModule (ρ : G → A) (X : Set G) (L : Set (G →₀ A)) : Submodule O (G → V) where
  carrier := {c | IsLocallyConstant c ∧ (∀ g h, c (g * h) = c g + ρ g • c h) ∧
    (∀ g ∈ X, c g = 0) ∧ ∀ R ∈ L, Finsupp.linearCombination A c R = 0}
  add_mem' := by
    rintro c c' ⟨hc, hcoc, hX, hL⟩ ⟨hc', hcoc', hX', hL'⟩
    refine ⟨hc.add hc', fun g h ↦ ?_, fun g hg ↦ ?_, fun R hR ↦ ?_⟩
    · simp only [Pi.add_apply, hcoc, hcoc', smul_add]
      abel
    · simp [hX g hg, hX' g hg]
    · have h₁ := hL R hR
      have h₂ := hL' R hR
      rw [Finsupp.linearCombination_apply] at h₁ h₂ ⊢
      simp only [Pi.add_apply, smul_add, Finsupp.sum_add, h₁, h₂, add_zero]
  zero_mem' := ⟨IsLocallyConstant.const 0, by simp, by simp, by simp⟩
  smul_mem' := by
    rintro r c ⟨hc, hcoc, hX, hL⟩
    refine ⟨hc.comp (r • ·), fun g h ↦ ?_, fun g hg ↦ ?_, fun R hR ↦ ?_⟩
    · simp only [Pi.smul_apply, hcoc, smul_add, smul_comm r (ρ g)]
    · simp [hX g hg]
    · have h := hL R hR
      rw [Finsupp.linearCombination_apply] at h ⊢
      simp only [Pi.smul_apply, smul_comm _ r, ← Finsupp.smul_sum, h, smul_zero]

variable {O V} {ρ : G → A} {X : Set G} {L : Set (G →₀ A)} {c : G → V}

/-- Membership in the Selmer module: `c` is a locally constant `ρ`-cocycle vanishing on `X` and
obeying every relation of `L`. -/
@[simp]
theorem mem_cocycleSelmerModule_iff :
    c ∈ cocycleSelmerModule O V ρ X L ↔ IsLocallyConstant c ∧
      (∀ g h, c (g * h) = c g + ρ g • c h) ∧ (∀ g ∈ X, c g = 0) ∧
        ∀ R ∈ L, Finsupp.linearCombination A c R = 0 :=
  Iff.rfl

/-- A member of the Selmer module is locally constant. -/
theorem isLocallyConstant_of_mem_cocycleSelmerModule (hc : c ∈ cocycleSelmerModule O V ρ X L) :
    IsLocallyConstant c :=
  hc.1

/-- A member of the Selmer module is a `ρ`-cocycle. -/
theorem apply_mul_of_mem_cocycleSelmerModule (hc : c ∈ cocycleSelmerModule O V ρ X L) (g h : G) :
    c (g * h) = c g + ρ g • c h :=
  hc.2.1 g h

/-- A member of the Selmer module vanishes on `X`. -/
theorem apply_eq_zero_of_mem_cocycleSelmerModule (hc : c ∈ cocycleSelmerModule O V ρ X L) {g : G}
    (hg : g ∈ X) : c g = 0 :=
  hc.2.2.1 g hg

/-- A member of the Selmer module obeys every relation of `L`. -/
theorem linearCombination_eq_zero_of_mem_cocycleSelmerModule
    (hc : c ∈ cocycleSelmerModule O V ρ X L) {R : G →₀ A} (hR : R ∈ L) :
    Finsupp.linearCombination A c R = 0 :=
  hc.2.2.2 R hR

/-- **The Selmer module is antitone in the conditions**: dropping vanishing conditions and
relations gives a larger module. -/
theorem cocycleSelmerModule_anti {X' : Set G} {L' : Set (G →₀ A)} (hX : X' ⊆ X) (hL : L' ⊆ L) :
    cocycleSelmerModule O V ρ X L ≤ cocycleSelmerModule O V ρ X' L' :=
  fun _ ⟨hc, hcoc, hX₀, hL₀⟩ ↦ ⟨hc, hcoc, fun g hg ↦ hX₀ g (hX hg), fun R hR ↦ hL₀ R (hL hR)⟩

end Definition

section Coboundary

variable {G : Type*} [Mul G] [TopologicalSpace G] {O : Type*} {A : Type*} [CommSemiring O]
  [Semiring A] [Algebra O A] {V : Type*} [AddCommGroup V] [Module A V] [Module O V]
  [IsScalarTower O A V] {ρ : G → A}

/-- **Coboundaries are cocycles.** If `ρ` is multiplicative, then for `v : V` with
`g ↦ ρ g • v` locally constant, the coboundary `g ↦ ρ g • v - v` lies in the Selmer module with
no vanishing conditions and no relations. -/
theorem smul_sub_mem_cocycleSelmerModule (hmul : ∀ g h, ρ (g * h) = ρ g * ρ h) {v : V}
    (hv : IsLocallyConstant fun g ↦ ρ g • v) :
    (fun g ↦ ρ g • v - v) ∈ cocycleSelmerModule O V ρ ∅ ∅ := by
  refine ⟨hv.sub (IsLocallyConstant.const v), fun g h ↦ ?_, by simp, by simp⟩
  simp only [hmul, mul_smul, smul_sub]
  abel

end Coboundary

section Map

variable {G : Type*} [Mul G] [TopologicalSpace G] (O : Type*) {A : Type*} [CommSemiring O]
  [Semiring A] [Algebra O A] {V W U : Type*} [AddCommMonoid V] [Module A V] [Module O V]
  [IsScalarTower O A V] [AddCommMonoid W] [Module A W] [Module O W] [IsScalarTower O A W]
  [AddCommMonoid U] [Module A U] [Module O U] [IsScalarTower O A U]
  {ρ : G → A} {X : Set G} {L : Set (G →₀ A)} {c : G → V} {f : V →ₗ[A] W}

variable {O} in
/-- **Composition with an `A`-linear map of coefficients preserves the Selmer module.** -/
theorem comp_mem_cocycleSelmerModule (hc : c ∈ cocycleSelmerModule O V ρ X L) :
    f ∘ c ∈ cocycleSelmerModule O W ρ X L := by
  obtain ⟨hc, hcoc, hX, hL⟩ := hc
  refine ⟨hc.comp f, fun g h ↦ ?_, fun g hg ↦ ?_, fun R hR ↦ ?_⟩
  · simp [hcoc]
  · simp [hX g hg]
  · rw [← Finsupp.apply_linearCombination, hL R hR, map_zero]

variable {O} in
/-- **An injective map of coefficients preserves and reflects the Selmer module**: for `f`
injective, `f ∘ c` is a member exactly when `c` is. -/
theorem comp_mem_cocycleSelmerModule_iff (hf : Injective f) :
    f ∘ c ∈ cocycleSelmerModule O W ρ X L ↔ c ∈ cocycleSelmerModule O V ρ X L := by
  refine ⟨fun ⟨hc, hcoc, hX, hL⟩ ↦ ⟨hc.desc _ _ hf, fun g h ↦ hf ?_, fun g hg ↦ hf ?_,
    fun R hR ↦ hf ?_⟩, comp_mem_cocycleSelmerModule⟩
  · simpa using hcoc g h
  · simpa using hX g hg
  · rw [Finsupp.apply_linearCombination, hL R hR, map_zero]

/-- For an injective map of coefficients `f : V → W`, the Selmer module with coefficients `V` is
the preimage of the one with coefficients `W` under composition with `f`. -/
theorem cocycleSelmerModule_eq_comap (hf : Injective f) :
    cocycleSelmerModule O V ρ X L =
      (cocycleSelmerModule O W ρ X L).comap ((f.restrictScalars O).compLeft G) :=
  Submodule.ext fun _ ↦ (comp_mem_cocycleSelmerModule_iff hf).symm

variable (ρ X L) in
/-- **Functoriality in the coefficients**: composition with an `A`-linear map `f : V → W`, as an
`O`-linear map `Sel(ρ, X, L; V) → Sel(ρ, X, L; W)`. -/
def cocycleSelmerModuleMap (f : V →ₗ[A] W) :
    cocycleSelmerModule O V ρ X L →ₗ[O] cocycleSelmerModule O W ρ X L :=
  ((f.restrictScalars O).compLeft G).restrict fun _ ↦ comp_mem_cocycleSelmerModule

/-- The image of a cocycle under `cocycleSelmerModuleMap` is its composition with `f`. -/
@[simp]
theorem coe_cocycleSelmerModuleMap_apply (c : cocycleSelmerModule O V ρ X L) :
    (cocycleSelmerModuleMap O ρ X L f c : G → W) = f ∘ c :=
  (rfl)

variable (ρ X L V) in
/-- Composition with the identity is the identity. -/
@[simp]
theorem cocycleSelmerModuleMap_id :
    cocycleSelmerModuleMap O ρ X L (LinearMap.id : V →ₗ[A] V) = LinearMap.id :=
  (rfl)

/-- Composition with `g ∘ f` is composition with `f` followed by composition with `g`. -/
theorem cocycleSelmerModuleMap_comp (g : W →ₗ[A] U) :
    cocycleSelmerModuleMap O ρ X L (g ∘ₗ f) =
      cocycleSelmerModuleMap O ρ X L g ∘ₗ cocycleSelmerModuleMap O ρ X L f :=
  (rfl)

/-- Composition with an injective map of coefficients is injective. -/
theorem cocycleSelmerModuleMap_injective (hf : Injective f) :
    Injective (cocycleSelmerModuleMap O ρ X L f) :=
  fun _ _ h ↦ Subtype.ext (hf.comp_left (congrArg Subtype.val h))

/-- **Torsion coefficients.** If `f : V → W` is injective with image the `a`-torsion of `W`,
composition with `f` maps the Selmer module with coefficients `V` onto the `a`-torsion of the
Selmer module with coefficients `W`. -/
theorem range_cocycleSelmerModuleMap (hf : Injective f) {a : O}
    (hrange : LinearMap.range (f.restrictScalars O) = torsionBy O W a) :
    LinearMap.range (cocycleSelmerModuleMap O ρ X L f) =
      torsionBy O (cocycleSelmerModule O W ρ X L) a := by
  have hmem (w : W) : w ∈ torsionBy O W a ↔ ∃ v, f v = w := by
    rw [← hrange, LinearMap.mem_range, LinearMap.coe_restrictScalars]
  ext ⟨c, hc⟩
  rw [LinearMap.mem_range, mem_torsionBy_iff, Subtype.ext_iff, Submodule.coe_smul,
    ZeroMemClass.coe_zero, funext_iff]
  simp only [Pi.smul_apply, Pi.zero_apply, Subtype.ext_iff, coe_cocycleSelmerModuleMap_apply]
  refine ⟨fun ⟨c', hc'⟩ g ↦ ?_, fun h ↦ ?_⟩
  · rw [← hc', ← mem_torsionBy_iff, hmem]
    exact ⟨_, rfl⟩
  · choose c' hc' using fun g ↦ (hmem (c g)).mp ((mem_torsionBy_iff _ _).mpr (h g))
    have hfc : f ∘ c' = c := funext hc'
    exact ⟨⟨c', (comp_mem_cocycleSelmerModule_iff hf).mp (hfc ▸ hc)⟩, hfc⟩

end Map

section Length

variable {G : Type*} [Mul G] [TopologicalSpace G] {O : Type*} {A : Type*} [CommRing O]
  [Semiring A] [Algebra O A] {V W : Type*} [AddCommGroup V] [Module A V] [Module O V]
  [IsScalarTower O A V] [AddCommGroup W] [Module A W] [Module O W] [IsScalarTower O A W]
  {ρ : G → A} {X : Set G} {L : Set (G →₀ A)} {f : V →ₗ[A] W}

/-- An injective map of coefficients does not decrease the length of the Selmer module. -/
theorem length_cocycleSelmerModule_le_of_injective (hf : Injective f) :
    Module.length O (cocycleSelmerModule O V ρ X L) ≤
      Module.length O (cocycleSelmerModule O W ρ X L) :=
  Module.length_le_of_injective _ (cocycleSelmerModuleMap_injective O hf)

/-- If `f : V → W` is injective with image the `a`-torsion of `W`, the Selmer module with
coefficients `V` has the length of the `a`-torsion of the Selmer module with coefficients `W`. -/
theorem length_cocycleSelmerModule_eq_length_torsionBy (hf : Injective f) {a : O}
    (hrange : LinearMap.range (f.restrictScalars O) = torsionBy O W a) :
    Module.length O (cocycleSelmerModule O V ρ X L) =
      Module.length O (torsionBy O (cocycleSelmerModule O W ρ X L) a) :=
  ((LinearEquiv.ofInjective _ (cocycleSelmerModuleMap_injective O hf)).trans
    (LinearEquiv.ofEq _ _ (range_cocycleSelmerModuleMap O hf hrange))).length_eq

end Length

section Matrix

open _root_.IsDiscreteValuationRing Matrix.Module

variable {G : Type*} [Mul G] [TopologicalSpace G] {O : Type*} [CommRing O] {n : Type*}
  [Fintype n] [DecidableEq n] (ρ : G → Matrix n n O) (X : Set G) (L : Set (G →₀ Matrix n n O))
  {M N : Type*} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N] {a : O}

/-- **Torsion coefficients, for matrix representations.** If `f : M → N` is injective with image
the `a`-torsion of `N`, for instance `f : O/a → B`, then composition with `f` applied in each
coordinate maps the Selmer module with coefficients `Mⁿ` onto the `a`-torsion of the Selmer
module with coefficients `Nⁿ`. -/
theorem range_cocycleSelmerModuleMap_mapMatrixModule {f : M →ₗ[O] N} (hf : Injective f)
    (hrange : LinearMap.range f = torsionBy O N a) :
    LinearMap.range (cocycleSelmerModuleMap O ρ X L (f.mapMatrixModule n)) =
      torsionBy O (cocycleSelmerModule O (n → N) ρ X L) a := by
  refine range_cocycleSelmerModuleMap O hf.comp_left ?_
  -- As an `O`-linear map, `f.mapMatrixModule n` is `f.compLeft n`, whose image is the product of
  -- the images of `f`, that is the `a`-torsion of `Nⁿ`.
  have h : (f.mapMatrixModule n).restrictScalars O = f.compLeft n := LinearMap.ext fun _ ↦ rfl
  ext w
  simp [h, LinearMap.range_compLeft, hrange, Submodule.mem_pi, funext_iff]

variable (K : Type*) [Field K] [Algebra O K] [IsFractionRing O K]

/-- **Torsion and divisible coefficients.** For `ρ : G → Mₙ(O)` over a domain `O` with fraction
field `K` and `a ≠ 0`, the Selmer module with coefficients `(O/a)ⁿ` has the length of the
`a`-torsion of the Selmer module with coefficients `(K/O)ⁿ`. -/
theorem length_cocycleSelmerModule_quotient_eq_length_torsionBy (ha : a ≠ 0) :
    Module.length O (cocycleSelmerModule O (n → O ⧸ Ideal.span {a}) ρ X L) =
      Module.length O (torsionBy O
        (cocycleSelmerModule O (n → K ⧸ LinearMap.range (Algebra.linearMap O K)) ρ X L) a) :=
  ((LinearEquiv.ofInjective _
    (cocycleSelmerModuleMap_injective O (divQuotient_injective (K := K) ha).comp_left)).trans
    (LinearEquiv.ofEq _ _ (range_cocycleSelmerModuleMap_mapMatrixModule ρ X L
      (divQuotient_injective ha) (range_divQuotient ha)))).length_eq

/-- **The divisible Selmer length bounds the torsion ones.** For `ρ : G → Mₙ(O)` over a domain `O`
with fraction field `K` and `a ≠ 0`, the length of the Selmer module with coefficients `(O/a)ⁿ` is
at most the length of the Selmer module with coefficients `(K/O)ⁿ`. -/
theorem length_cocycleSelmerModule_quotient_le (ha : a ≠ 0) :
    Module.length O (cocycleSelmerModule O (n → O ⧸ Ideal.span {a}) ρ X L) ≤
      Module.length O
        (cocycleSelmerModule O (n → K ⧸ LinearMap.range (Algebra.linearMap O K)) ρ X L) :=
  length_cocycleSelmerModule_le_of_injective
    (f := (divQuotient (K := K) a).mapMatrixModule n) (divQuotient_injective ha).comp_left

end Matrix

end TauCeti
