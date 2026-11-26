/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.DirectSum
public import Mathlib.Algebra.Lie.Quotient
public import TauCeti.RepresentationTheory.GFinite
public import TauCeti.RepresentationTheory.Isotypic
public import TauCeti.RepresentationTheory.LieHom

/-!
# `(𝔤, K)`-modules

Let `𝔤` be a Lie algebra over a field `k` and let a group `K` act on `𝔤` by Lie algebra
endomorphisms through a representation `Ad` (`Representation.IsLieAction Ad`, from
`TauCeti/RepresentationTheory/LieHom.lean`); the definitions only use that `K` is a monoid. A
`(𝔤, K)`-module is a `𝔤`-module `V` (a Lie module over `k`) with a representation `ρ` of `K` on `V`
which is covariant, `ρ g ⁅x, v⁆ = ⁅Ad g x, ρ g v⁆`, and locally finite: every vector is `K`-finite
(`Representation.IsGFinite`), that is, its orbit spans a finite-dimensional subspace.

This file records the algebraic part of the theory, which needs neither a topology nor a Lie group
structure on `K`. For a real reductive group with maximal compact subgroup `K` and complexified Lie
algebra `𝔤`, a `(𝔤, K)`-module in the sense of harmonic analysis also asks that `K` act smoothly
on each finite-dimensional `K`-stable subspace with differential the action of `Lie K ⊆ 𝔤`. That
condition is the further predicate `TauCeti.GKModule.IsCompatible` on a `TauCeti.GKModule`
(`TauCeti/RepresentationTheory/GKModule/Compatible.lean`); nothing below uses it.

## Main definitions

* `TauCeti.GKModule Ad V`: a `(𝔤, K)`-module structure on the `𝔤`-module `V`.
* `TauCeti.GKSubmodule M`: a `(𝔤, K)`-submodule, a Lie submodule stable under `K`.
* `TauCeti.GKModule.submodule`, `TauCeti.GKModule.quotient`: the `(𝔤, K)`-module structures on a
  `(𝔤, K)`-submodule and on the quotient by it.
* `TauCeti.GKModule.directSum`: the direct sum of a family of `(𝔤, K)`-modules.
* `TauCeti.GKModule.IsHarishChandraModule`: admissible and finitely generated over `𝔤`, that is,
  over the enveloping algebra `U(𝔤)`.

Isotypic components, multiplicities and admissibility only involve the action of `K`, so they are
stated for representations: the `σ`-isotypic component of `M` is
`Representation.isotypicComponent M.ρ σ` (`TauCeti/RepresentationTheory/Isotypic.lean`), which is
`K`-stable but not `𝔤`-stable in general since `𝔤` moves `K`-types; the multiplicity of `σ` is
`Representation.multiplicity M.ρ σ`, the dimension of `Hom_K(σ, V)`; and `M` is admissible when
its `K`-action has finite multiplicities, `Representation.HasFiniteMultiplicities M.ρ`
(`TauCeti/RepresentationTheory/Admissible.lean`).

## Main statements

* `TauCeti.GKModule.hasFiniteMultiplicities_submodule`,
  `TauCeti.GKModule.hasFiniteMultiplicities_directSum`: admissibility passes to `(𝔤, K)`-submodules
  and to finite direct sums.
* `TauCeti.GKModule.isHarishChandraModule_of_finiteDimensional`: a finite-dimensional
  `(𝔤, K)`-module is a Harish-Chandra module.

## References

* J. Bernstein and B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*, Israel J.
  Math. 199 (2014), 45–111, §4.1.
* N. R. Wallach, *Real Reductive Groups I*, Academic Press (1988), Chapter 3.
-/

public section

namespace TauCeti

open Representation

universe v

variable {k 𝔤 K : Type*} [Field k] [LieRing 𝔤] [LieAlgebra k 𝔤] [Monoid K]

/-- A **`(𝔤, K)`-module** structure on a `𝔤`-module `V`, for a monoid `K` acting on the Lie algebra
`𝔤` by Lie algebra endomorphisms through `Ad`: a representation `ρ` of `K` on `V` with
`ρ g ⁅x, v⁆ = ⁅Ad g x, ρ g v⁆`, under which every vector is `K`-finite. -/
structure GKModule (Ad : Representation k K 𝔤) [IsLieAction Ad] (V : Type v) [AddCommGroup V]
    [Module k V] [LieRingModule 𝔤 V] [LieModule k 𝔤 V] where
  /-- The action of `K`. -/
  ρ : Representation k K V
  /-- The action of `K` is covariant for the actions of `K` on `𝔤` and of `𝔤` on `V`. -/
  map_lie (g : K) (x : 𝔤) (v : V) : ρ g ⁅x, v⁆ = ⁅Ad g x, ρ g v⁆
  /-- Every vector is `K`-finite. -/
  isGFinite (v : V) : ρ.IsGFinite v

variable {Ad : Representation k K 𝔤} [IsLieAction Ad] {V : Type v} [AddCommGroup V]
  [Module k V] [LieRingModule 𝔤 V] [LieModule k 𝔤 V]

/-- A `(𝔤, K)`-module structure is determined by its action of `K`. -/
@[ext]
theorem GKModule.ext {M M' : GKModule Ad V} (h : M.ρ = M'.ρ) : M = M' := by
  cases M
  cases M'
  cases h
  rfl

/-- A **`(𝔤, K)`-submodule** of a `(𝔤, K)`-module: a Lie submodule stable under `K`. -/
structure GKSubmodule (M : GKModule Ad V) where
  /-- The underlying Lie submodule. -/
  toLieSubmodule : LieSubmodule k 𝔤 V
  /-- The submodule is stable under `K`. -/
  apply_mem (g : K) {v : V} : v ∈ toLieSubmodule → M.ρ g v ∈ toLieSubmodule

namespace GKSubmodule

variable {M : GKModule Ad V}

theorem toLieSubmodule_injective :
    Function.Injective (toLieSubmodule : GKSubmodule M → LieSubmodule k 𝔤 V) := by
  rintro ⟨_, _⟩ ⟨_, _⟩ rfl
  rfl

/-- A `(𝔤, K)`-submodule is determined by its underlying Lie submodule. -/
@[simp]
theorem toLieSubmodule_inj {N N' : GKSubmodule M} :
    N.toLieSubmodule = N'.toLieSubmodule ↔ N = N' :=
  toLieSubmodule_injective.eq_iff

instance instSetLike : SetLike (GKSubmodule M) V where
  coe N := N.toLieSubmodule
  coe_injective := SetLike.coe_injective.comp toLieSubmodule_injective

@[simp]
theorem mem_toLieSubmodule {N : GKSubmodule M} {v : V} : v ∈ N.toLieSubmodule ↔ v ∈ N :=
  Iff.rfl

@[ext]
theorem ext {N N' : GKSubmodule M} (h : ∀ v, v ∈ N ↔ v ∈ N') : N = N' :=
  SetLike.ext h

/-- The subrepresentation of `K` underlying a `(𝔤, K)`-submodule. -/
def toSubrepresentation (N : GKSubmodule M) : Subrepresentation M.ρ where
  toSubmodule := N.toLieSubmodule.toSubmodule
  apply_mem_toSubmodule g _ hv := N.apply_mem g hv

@[simp]
theorem mem_toSubrepresentation {N : GKSubmodule M} {v : V} :
    v ∈ N.toSubrepresentation ↔ v ∈ N :=
  Iff.rfl

end GKSubmodule

namespace GKModule

variable (M : GKModule Ad V)

/-! ### Submodules and quotients -/

section SubQuotient

variable (N : GKSubmodule M)

/-- The `(𝔤, K)`-module structure on a `(𝔤, K)`-submodule. -/
def submodule : GKModule Ad N.toLieSubmodule where
  ρ := N.toSubrepresentation.toRepresentation
  map_lie g x v := Subtype.ext (M.map_lie g x v)
  isGFinite v := IsGFinite.of_injective N.toSubrepresentation.subtype
    N.toSubrepresentation.subtype_injective (by simpa using M.isGFinite v)

@[simp]
theorem submodule_ρ_apply_coe (g : K) (v : N.toLieSubmodule) :
    (((M.submodule N).ρ g v : N.toLieSubmodule) : V) = M.ρ g v :=
  (rfl)

/-- The `(𝔤, K)`-module structure on the quotient by a `(𝔤, K)`-submodule. -/
def quotient : GKModule Ad (V ⧸ N.toLieSubmodule) where
  ρ := M.ρ.quotient N.toLieSubmodule.toSubmodule fun g _ hv ↦ N.apply_mem g hv
  map_lie g x v := by
    induction v using Submodule.Quotient.induction_on with | H v => ?_
    -- Here `ρ` is `Representation.quotient` on `V ⧸ N.toLieSubmodule.toSubmodule`, applied to
    -- elements of the Lie quotient `V ⧸ N.toLieSubmodule`, which carries the same module structure
    -- only up to unfolding, so `simp` cannot use `Representation.quotient_apply` here. Both sides
    -- reduce by definition (of `mapQ` and of the quotient bracket) to `mk` applied to the two
    -- sides of `M.map_lie g x v`.
    exact congrArg (Submodule.Quotient.mk (p := N.toLieSubmodule.toSubmodule)) (M.map_lie g x v)
  isGFinite v := by
    induction v using Submodule.Quotient.induction_on with | H v => ?_
    have := (isGFinite_iff _ _).1 (M.isGFinite v)
    exact IsGFinite.of_apply_eq N.toLieSubmodule.toSubmodule.mkQ (u := fun g ↦ M.ρ g v)
      fun g ↦ by simp

@[simp]
theorem quotient_ρ_apply_mk (g : K) (v : V) :
    (M.quotient N).ρ g (LieSubmodule.Quotient.mk v) = LieSubmodule.Quotient.mk (M.ρ g v) :=
  (rfl)

end SubQuotient

/-! ### Direct sums -/

section DirectSum

open DirectSum

variable {ι : Type*} {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
  [∀ i, LieRingModule 𝔤 (V i)] [∀ i, LieModule k 𝔤 (V i)]

/-- The `(𝔤, K)`-module structure on a direct sum of `(𝔤, K)`-modules. Every vector of the direct
sum has finitely many nonzero components, so the family may be infinite. -/
noncomputable def directSum (M : ∀ i, GKModule Ad (V i)) : GKModule Ad (⨁ i, V i) where
  ρ := Representation.directSum fun i ↦ (M i).ρ
  map_lie g x v := by
    ext i
    simp [(M i).map_lie]
  isGFinite v := by
    classical
    induction v using DirectSum.induction_on with
    | zero => exact IsGFinite.zero
    | of i v =>
      have := (isGFinite_iff _ _).1 ((M i).isGFinite v)
      exact IsGFinite.of_apply_eq (lof k ι V i) (u := fun g ↦ (M i).ρ g v) fun g ↦ by
        simp [lof_eq_of]
    | add v v' hv hv' => exact hv.add hv'

@[simp]
theorem directSum_ρ_apply_apply (M : ∀ i, GKModule Ad (V i)) (g : K) (v : ⨁ i, V i) (i : ι) :
    (directSum M).ρ g v i = (M i).ρ g (v i) := by
  simp [directSum]

end DirectSum

/-! ### Admissible and Harish-Chandra modules -/

variable {M} in
/-- A `(𝔤, K)`-submodule of an admissible module is admissible. -/
theorem hasFiniteMultiplicities_submodule (hM : M.ρ.HasFiniteMultiplicities)
    (N : GKSubmodule M) : (M.submodule N).ρ.HasFiniteMultiplicities :=
  hM.subrepresentation N.toSubrepresentation

/-- A finite direct sum of admissible `(𝔤, K)`-modules is admissible. -/
theorem hasFiniteMultiplicities_directSum {ι : Type*} [Finite ι] {V : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] [∀ i, LieRingModule 𝔤 (V i)]
    [∀ i, LieModule k 𝔤 (V i)]
    {M : ∀ i, GKModule Ad (V i)} (hM : ∀ i, (M i).ρ.HasFiniteMultiplicities) :
    (directSum M).ρ.HasFiniteMultiplicities :=
  HasFiniteMultiplicities.directSum hM

/-- A **Harish-Chandra module** is an admissible `(𝔤, K)`-module that is finitely generated
over `𝔤`, that is, generated by a finite set as a module over the enveloping algebra `U(𝔤)`. The
Harish-Chandra modules of harmonic analysis on a real reductive group are those that are moreover
compatible with the Lie group structure of `K`, `TauCeti.GKModule.IsCompatible`. -/
def IsHarishChandraModule : Prop :=
  M.ρ.HasFiniteMultiplicities ∧ ∃ s : Finset V, LieSubmodule.lieSpan k 𝔤 (s : Set V) = ⊤

/-- A Harish-Chandra module is an admissible `(𝔤, K)`-module generated over `𝔤` by a finite set. -/
theorem isHarishChandraModule_iff :
    M.IsHarishChandraModule ↔
      M.ρ.HasFiniteMultiplicities ∧ ∃ s : Finset V, LieSubmodule.lieSpan k 𝔤 (s : Set V) = ⊤ :=
  Iff.rfl

variable {M} in
/-- A Harish-Chandra module is admissible. -/
theorem IsHarishChandraModule.hasFiniteMultiplicities (hM : M.IsHarishChandraModule) :
    M.ρ.HasFiniteMultiplicities :=
  hM.1

variable {M} in
/-- A Harish-Chandra module is generated over `𝔤` by a finite set. -/
theorem IsHarishChandraModule.exists_lieSpan_eq_top (hM : M.IsHarishChandraModule) :
    ∃ s : Finset V, LieSubmodule.lieSpan k 𝔤 (s : Set V) = ⊤ :=
  hM.2

/-- A finite-dimensional `(𝔤, K)`-module is a Harish-Chandra module. -/
theorem isHarishChandraModule_of_finiteDimensional [FiniteDimensional k V] :
    M.IsHarishChandraModule := by
  classical
  refine ⟨M.ρ.hasFiniteMultiplicities_of_finiteDimensional, ?_⟩
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := k) (M := V)
  refine ⟨s, eq_top_iff.2 fun v _ ↦ ?_⟩
  exact LieSubmodule.submodule_span_le_lieSpan (hs ▸ Submodule.mem_top)

end GKModule

end TauCeti
