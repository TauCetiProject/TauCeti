/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.DirectSum
public import Mathlib.Algebra.Lie.Quotient
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RingTheory.SimpleModule.Isotypic
public import TauCeti.RepresentationTheory.GFinite
public import TauCeti.RepresentationTheory.Irreducible

/-!
# `(𝔤, K)`-modules

Let `𝔤` be a Lie algebra over a field `k` and let a group `K` act on `𝔤` by Lie algebra
endomorphisms through a representation `Ad`; the definitions only use that `K` is a monoid. A
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

* `TauCeti.IsLieAction Ad`: `K` acts on `𝔤` by Lie algebra endomorphisms. By
  `TauCeti.IsLieAction.of_lieEquiv`, this holds when every `Ad g` underlies a Lie algebra
  automorphism.
* `TauCeti.GKModule Ad V`: a `(𝔤, K)`-module structure on the `𝔤`-module `V`.
* `TauCeti.GKSubmodule M`: a `(𝔤, K)`-submodule, a Lie submodule stable under `K`.
* `TauCeti.GKModule.submodule`, `TauCeti.GKModule.quotient`: the `(𝔤, K)`-module structures on a
  `(𝔤, K)`-submodule and on the quotient by it.
* `TauCeti.GKModule.directSum`: the direct sum of a family of `(𝔤, K)`-modules.
* `TauCeti.GKModule.isotypic M σ`: the `σ`-isotypic component, the sum of the images of the
  `K`-equivariant maps from `σ` to `V`. It is `K`-stable (`TauCeti.GKModule.isotypicSubrep`) but
  not `𝔤`-stable in general, since `𝔤` moves `K`-types.
* `TauCeti.GKModule.multiplicity M σ`: the dimension of `Hom_K(σ, V)` in `ℕ∞`, equal to `⊤` when
  it is infinite.
* `TauCeti.GKModule.IsAdmissible`: `Hom_K(σ, V)` is finite-dimensional for every irreducible `σ`.
* `TauCeti.GKModule.IsHarishChandraModule`: admissible and finitely generated over `𝔤`, that is,
  over the enveloping algebra `U(𝔤)`.

## Main statements

* `TauCeti.GKModule.mem_isotypic_iff`: for irreducible `σ`, the isotypic component is Mathlib's
  `isotypicComponent` of the simple `k[K]`-module `σ.asModule`.
* `TauCeti.GKModule.evalIntertwiningMap_injective`: for irreducible `σ` and `w ≠ 0`, evaluation at
  `w` embeds `Hom_K(σ, V)` into the isotypic component `V(σ)`.
* `TauCeti.GKModule.IsAdmissible.of_finiteDimensional_isotypic`: finite-dimensional isotypic
  components give an admissible module.
* `TauCeti.GKModule.IsAdmissible.finiteDimensional`: in an admissible module, `Hom_K(σ, V)` is
  finite-dimensional for every irreducible `σ`.
* `TauCeti.GKModule.IsAdmissible.submodule`, `TauCeti.GKModule.IsAdmissible.directSum`:
  admissibility passes to `(𝔤, K)`-submodules and to finite direct sums.
* `TauCeti.GKModule.isHarishChandraModule_of_finiteDimensional`: a finite-dimensional
  `(𝔤, K)`-module is a Harish-Chandra module.

## Implementation notes

The multiplicity is the dimension of `Hom_K(σ, V)`. For irreducible `σ` with `Hom_K(σ, V)`
finite-dimensional, when `k` is not algebraically closed this is the number of copies of `σ` in
`V(σ)` multiplied by the dimension of the division algebra `End_K(σ)`. Admissibility is
quantified over the irreducible subrepresentations of `V`, which avoids fixing a universe for `σ`:
an irreducible representation with a nonzero map to `V` is isomorphic to its image.

## References

* J. Bernstein and B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*, Israel J.
  Math. 199 (2014), 45–111, §4.1.
* N. R. Wallach, *Real Reductive Groups I*, Academic Press (1988), Chapter 3.
-/

public section

namespace TauCeti

open Representation

universe v w

variable {k 𝔤 K : Type*} [Field k] [LieRing 𝔤] [LieAlgebra k 𝔤] [Monoid K]

/-- A representation `Ad` of a monoid `K` on a Lie algebra `𝔤` **acts by Lie algebra
endomorphisms** when every `Ad g` preserves the Lie bracket. -/
class IsLieAction (Ad : Representation k K 𝔤) : Prop where
  /-- Every `Ad g` preserves the Lie bracket. -/
  map_lie (g : K) (x y : 𝔤) : Ad g ⁅x, y⁆ = ⁅Ad g x, Ad g y⁆

/-- A representation whose operators are the linear maps underlying Lie algebra endomorphisms
`φ g` acts by Lie algebra endomorphisms. -/
theorem IsLieAction.of_lieHom {Ad : Representation k K 𝔤} (φ : K → 𝔤 →ₗ⁅k⁆ 𝔤)
    (h : ∀ g x, φ g x = Ad g x) : IsLieAction Ad where
  map_lie g x y := by simp only [← h, LieHom.map_lie]

/-- A representation whose operators are the linear maps underlying Lie algebra automorphisms
`φ g` acts by Lie algebra endomorphisms. -/
theorem IsLieAction.of_lieEquiv {Ad : Representation k K 𝔤} (φ : K → 𝔤 ≃ₗ⁅k⁆ 𝔤)
    (h : ∀ g x, φ g x = Ad g x) : IsLieAction Ad :=
  .of_lieHom (fun g ↦ (φ g : 𝔤 →ₗ⁅k⁆ 𝔤)) h

/-- The trivial representation acts by Lie algebra endomorphisms. -/
instance IsLieAction.instTrivial : IsLieAction (Representation.trivial k K 𝔤) :=
  .of_lieHom (fun _ ↦ 1) fun _ _ ↦ rfl

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
  ρ :=
    { toFun g :=
        { toFun v := ⟨M.ρ g v, N.apply_mem g v.property⟩
          map_add' _ _ := Subtype.ext (map_add _ _ _)
          map_smul' _ _ := Subtype.ext (map_smul _ _ _) }
      map_one' := by ext; simp
      map_mul' _ _ := by ext; simp }
  map_lie g x v := Subtype.ext (M.map_lie g x v)
  isGFinite v := by
    let f : N.toLieSubmodule →ₗ[k] V := N.toLieSubmodule.toSubmodule.subtype
    have hf : Function.Injective f := Subtype.val_injective
    have hv := M.isGFinite (v : V)
    rw [isGFinite_iff] at hv ⊢
    have : FiniteDimensional k ((Submodule.span k (Set.range fun g : K =>
        (⟨M.ρ g v, N.apply_mem g v.property⟩ : N.toLieSubmodule))).map f) := by
      rw [Submodule.map_span, ← Set.range_comp]
      exact hv
    exact LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective f hf _).symm

@[simp]
theorem submodule_ρ_apply_coe (g : K) (v : N.toLieSubmodule) :
    (((M.submodule N).ρ g v : N.toLieSubmodule) : V) = M.ρ g v :=
  (rfl)

/-- The `(𝔤, K)`-module structure on the quotient by a `(𝔤, K)`-submodule. -/
def quotient : GKModule Ad (V ⧸ N.toLieSubmodule) where
  ρ := M.ρ.quotient N.toLieSubmodule.toSubmodule fun g _ hv ↦ N.apply_mem g hv
  map_lie g x v := by
    induction v using Submodule.Quotient.induction_on with | H v => ?_
    exact congrArg (Submodule.Quotient.mk (p := N.toLieSubmodule.toSubmodule)) (M.map_lie g x v)
  isGFinite v := by
    induction v using Submodule.Quotient.induction_on with | H v => ?_
    have hv := M.isGFinite v
    rw [isGFinite_iff] at hv
    exact IsGFinite.of_apply_eq (N.toLieSubmodule.toSubmodule.mkQ) fun g ↦ rfl

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
      have hv := (M i).isGFinite v
      rw [isGFinite_iff] at hv
      exact IsGFinite.of_apply_eq (lof k ι V i) (u := fun g ↦ (M i).ρ g v) fun g ↦ by
        simp [lof_eq_of]
    | add v v' hv hv' => exact hv.add hv'

@[simp]
theorem directSum_ρ_apply_apply (M : ∀ i, GKModule Ad (V i)) (g : K) (v : ⨁ i, V i) (i : ι) :
    (directSum M).ρ g v i = (M i).ρ g (v i) := by
  simp [directSum]

end DirectSum

/-! ### Isotypic components and multiplicities -/

section Isotypic

variable {W : Type*} [AddCommGroup W] [Module k W] (σ : Representation k K W)

/-- The **`σ`-isotypic component** `V(σ)` of a `(𝔤, K)`-module: the sum of the images of the
`K`-equivariant linear maps from `σ` to `V`. For irreducible `σ` it is the sum of the
subrepresentations isomorphic to `σ`. It is stable under `K` (`TauCeti.GKModule.isotypicSubrep`)
but in general not under `𝔤`. -/
def isotypic : Submodule k V :=
  ⨆ f : IntertwiningMap σ M.ρ, LinearMap.range f.toLinearMap

variable {σ} in
theorem range_le_isotypic (f : IntertwiningMap σ M.ρ) :
    LinearMap.range f.toLinearMap ≤ M.isotypic σ :=
  le_iSup (fun f : IntertwiningMap σ M.ρ ↦ LinearMap.range f.toLinearMap) f

variable {σ} in
theorem apply_mem_isotypic (f : IntertwiningMap σ M.ρ) (w : W) : f w ∈ M.isotypic σ :=
  M.range_le_isotypic f ⟨w, rfl⟩

variable {σ} in
/-- The isotypic component is stable under `K`. -/
theorem ρ_apply_mem_isotypic (g : K) {v : V} (hv : v ∈ M.isotypic σ) :
    M.ρ g v ∈ M.isotypic σ := by
  refine Submodule.iSup_induction _ (motive := fun v ↦ M.ρ g v ∈ M.isotypic σ) hv ?_ ?_ ?_
  · rintro f _ ⟨w, rfl⟩
    rw [IntertwiningMap.toLinearMap_apply, ← f.isIntertwining]
    exact M.apply_mem_isotypic f _
  · simp
  · intro v v' hv hv'
    simpa using add_mem hv hv'

open scoped MonoidAlgebra in
variable {σ} in
/-- For irreducible `σ`, the isotypic component is Mathlib's `isotypicComponent` of the simple
`k[K]`-module `σ.asModule` in `V`, read on `V` through `Representation.asModuleEquiv`. -/
theorem mem_isotypic_iff [σ.IsIrreducible] {v : V} :
    v ∈ M.isotypic σ ↔
      M.ρ.asModuleEquiv.symm v ∈ isotypicComponent k[K] M.ρ.asModule σ.asModule := by
  constructor
  · intro hv
    refine Submodule.iSup_induction _
      (motive := fun v ↦ M.ρ.asModuleEquiv.symm v ∈ isotypicComponent k[K] _ _) hv ?_ ?_ ?_
    · rintro f _ ⟨w, rfl⟩
      let F := IntertwiningMap.equivLinearMapAsModule σ M.ρ f
      have hF : LinearMap.range F ≤ isotypicComponent k[K] M.ρ.asModule σ.asModule := by
        obtain inj | eq := F.injective_or_eq_zero
        · exact le_sSup ⟨(LinearEquiv.ofInjective F inj).symm⟩
        · simp [eq]
      exact hF ⟨σ.asModuleEquiv.symm w, rfl⟩
    · simp
    · intro v v' hv hv'
      simpa using add_mem hv hv'
  · intro hv
    rw [isotypicComponent, sSup_eq_iSup'] at hv
    rw [← M.ρ.asModuleEquiv.apply_symm_apply v]
    refine Submodule.iSup_induction _
      (motive := fun x ↦ M.ρ.asModuleEquiv x ∈ M.isotypic σ) hv ?_ ?_ ?_
    · rintro ⟨m, ⟨e⟩⟩ x hx
      let f := (IntertwiningMap.equivLinearMapAsModule σ M.ρ).symm (m.subtype ∘ₗ e.symm.toLinearMap)
      have : M.ρ.asModuleEquiv x = f (σ.asModuleEquiv (e ⟨x, hx⟩)) := by
        change _ = M.ρ.asModuleEquiv (m.subtype (e.symm (e ⟨x, hx⟩)))
        rw [LinearEquiv.symm_apply_apply]
        rfl
      rw [this]
      exact M.apply_mem_isotypic f _
    · simp
    · intro x y hx hy
      simpa using add_mem hx hy

/-- The isotypic component as a subrepresentation of `K`. -/
def isotypicSubrep : Subrepresentation M.ρ where
  toSubmodule := M.isotypic σ
  apply_mem_toSubmodule g _ hv := M.ρ_apply_mem_isotypic g hv

@[simp]
theorem mem_isotypicSubrep {v : V} : v ∈ M.isotypicSubrep σ ↔ v ∈ M.isotypic σ :=
  Iff.rfl

/-- The **multiplicity** of `σ` in a `(𝔤, K)`-module: the dimension of `Hom_K(σ, V)`, as an
element of `ℕ∞`, which is `⊤` when `Hom_K(σ, V)` is infinite-dimensional. -/
noncomputable def multiplicity : ℕ∞ :=
  (Module.rank k (IntertwiningMap σ M.ρ)).toENat

theorem multiplicity_def : M.multiplicity σ = (Module.rank k (IntertwiningMap σ M.ρ)).toENat :=
  (rfl)

/-- When `Hom_K(σ, V)` is finite-dimensional, the multiplicity is its `finrank`. -/
theorem multiplicity_eq_finrank [FiniteDimensional k (IntertwiningMap σ M.ρ)] :
    M.multiplicity σ = Module.finrank k (IntertwiningMap σ M.ρ) := by
  rw [multiplicity_def, ← Module.finrank_eq_rank, Cardinal.toENat_nat]

/-- The multiplicity is finite exactly when `Hom_K(σ, V)` is finite-dimensional. -/
theorem multiplicity_lt_top_iff :
    M.multiplicity σ < ⊤ ↔ FiniteDimensional k (IntertwiningMap σ M.ρ) := by
  rw [multiplicity_def, Cardinal.toENat_lt_top, Module.rank_lt_aleph0_iff]

/-- Evaluation of `K`-equivariant maps `σ → V` at a vector `w`, which lands in the isotypic
component `V(σ)`. -/
def evalIntertwiningMap (w : W) : IntertwiningMap σ M.ρ →ₗ[k] M.isotypic σ where
  toFun f := ⟨f w, M.apply_mem_isotypic f w⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem evalIntertwiningMap_apply_coe (w : W) (f : IntertwiningMap σ M.ρ) :
    (M.evalIntertwiningMap σ w f : V) = f w :=
  (rfl)

variable {σ} in
/-- For irreducible `σ`, evaluation at a nonzero vector is injective on `Hom_K(σ, V)`: a nonzero
equivariant map from an irreducible representation is injective. -/
theorem evalIntertwiningMap_injective [σ.IsIrreducible] {w : W} (hw : w ≠ 0) :
    Function.Injective (M.evalIntertwiningMap σ w) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  rcases IsIrreducible.injective_or_eq_zero f with hinj | h0
  · exact absurd (hinj (by simpa using congrArg Subtype.val hf)) hw
  · exact h0

variable {σ} in
/-- For irreducible `σ`, a finite-dimensional isotypic component `V(σ)` makes `Hom_K(σ, V)`
finite-dimensional. -/
theorem finiteDimensional_intertwiningMap_of_isotypic [σ.IsIrreducible]
    [FiniteDimensional k (M.isotypic σ)] : FiniteDimensional k (IntertwiningMap σ M.ρ) := by
  have := Representation.IsIrreducible.nontrivial (ρ := σ) inferInstance
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  exact Module.Finite.of_injective _ (M.evalIntertwiningMap_injective hw)

variable {σ} in
/-- For irreducible `σ`, the multiplicity is at most the dimension of the isotypic component. -/
theorem multiplicity_le_rank_isotypic [σ.IsIrreducible] :
    M.multiplicity σ ≤ (Module.rank k (M.isotypic σ)).toENat := by
  have := Representation.IsIrreducible.nontrivial (ρ := σ) inferInstance
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  have h := OrderHomClass.mono Cardinal.toENat
    (LinearMap.lift_rank_le_of_injective _ (M.evalIntertwiningMap_injective (σ := σ) hw))
  rwa [Cardinal.toENat_lift, Cardinal.toENat_lift] at h

end Isotypic

/-! ### Admissible and Harish-Chandra modules -/

/-- A `(𝔤, K)`-module is **admissible** when `Hom_K(σ, V)` is finite-dimensional for every
irreducible representation `σ` of `K`. Only an irreducible `σ` with a nonzero map to `V` can
violate this, and such a `σ` is isomorphic to its image, so the definition quantifies over the
irreducible subrepresentations of `V`; `TauCeti.GKModule.IsAdmissible.finiteDimensional` gives the
statement for every irreducible `σ`, in any universe. -/
def IsAdmissible : Prop :=
  ∀ U : Subrepresentation M.ρ, U.toRepresentation.IsIrreducible →
    FiniteDimensional k (IntertwiningMap U.toRepresentation M.ρ)

/-- A **Harish-Chandra module** is an admissible `(𝔤, K)`-module that is finitely generated
over `𝔤`, that is, generated by a finite set as a module over the enveloping algebra `U(𝔤)`. The
Harish-Chandra modules of harmonic analysis on a real reductive group are those that are moreover
compatible with the Lie group structure of `K`, `TauCeti.GKModule.IsCompatible`. -/
def IsHarishChandraModule : Prop :=
  M.IsAdmissible ∧ ∃ s : Finset V, LieSubmodule.lieSpan k 𝔤 (s : Set V) = ⊤

namespace IsAdmissible

variable {M}

/-- In an admissible `(𝔤, K)`-module, `Hom_K(σ, V)` is finite-dimensional for every irreducible
`σ`. -/
theorem finiteDimensional (hM : M.IsAdmissible) {W : Type w} [AddCommGroup W] [Module k W]
    (σ : Representation k K W) [hσ : σ.IsIrreducible] :
    FiniteDimensional k (IntertwiningMap σ M.ρ) := by
  by_cases h : ∃ f : IntertwiningMap σ M.ρ, f ≠ 0
  swap
  · push Not at h
    have : Subsingleton (IntertwiningMap σ M.ρ) := ⟨fun f f' ↦ (h f).trans (h f').symm⟩
    infer_instance
  obtain ⟨f, hf⟩ := h
  have hinj : Function.Injective f := (IsIrreducible.injective_or_eq_zero f).resolve_right hf
  let e : Representation.Equiv σ f.range.toRepresentation :=
    .mk (LinearEquiv.ofInjective f.toLinearMap hinj) fun g ↦ by
      ext w
      exact IntertwiningMap.isIntertwining _ _ f g w
  have := hM f.range (e.isIrreducible hσ)
  let c : IntertwiningMap σ M.ρ →ₗ[k] IntertwiningMap f.range.toRepresentation M.ρ :=
    { toFun φ := φ.comp e.symm.toIntertwiningMap
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  refine Module.Finite.of_injective c fun φ φ' h ↦ ?_
  ext w
  have h' := congr($h (e w))
  change φ (e.symm (e w)) = φ' (e.symm (e w)) at h'
  simpa using h'

/-- A `(𝔤, K)`-module in which `Hom_K(σ, V)` is finite-dimensional for every irreducible `σ` on a
carrier in the universe of `V` is admissible. -/
theorem of_forall
    (h : ∀ (W : Type v) [AddCommGroup W] [Module k W] (σ : Representation k K W),
      σ.IsIrreducible → FiniteDimensional k (IntertwiningMap σ M.ρ)) :
    M.IsAdmissible := fun U hU ↦ h U.toSubmodule U.toRepresentation hU

variable (M) in
/-- A `(𝔤, K)`-module whose isotypic components are finite-dimensional is admissible. -/
theorem of_finiteDimensional_isotypic
    (h : ∀ U : Subrepresentation M.ρ, U.toRepresentation.IsIrreducible →
      FiniteDimensional k (M.isotypic U.toRepresentation)) :
    M.IsAdmissible := fun U hU ↦
  have := h U hU
  M.finiteDimensional_intertwiningMap_of_isotypic

/-- A `(𝔤, K)`-submodule of an admissible module is admissible. -/
theorem submodule (hM : M.IsAdmissible) (N : GKSubmodule M) : (M.submodule N).IsAdmissible := by
  intro U hU
  have := hM.finiteDimensional U.toRepresentation
  let ι : IntertwiningMap (M.submodule N).ρ M.ρ :=
    ⟨N.toLieSubmodule.toSubmodule.subtype, fun _ ↦ rfl⟩
  let c : IntertwiningMap U.toRepresentation (M.submodule N).ρ →ₗ[k]
      IntertwiningMap U.toRepresentation M.ρ :=
    { toFun f := ι.comp f
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  refine Module.Finite.of_injective c fun f f' h ↦ ?_
  ext w
  exact congr($h w)

/-- A finite direct sum of admissible `(𝔤, K)`-modules is admissible. -/
theorem directSum {ι : Type*} [Finite ι] {V : ι → Type*} [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] [∀ i, LieRingModule 𝔤 (V i)] [∀ i, LieModule k 𝔤 (V i)]
    {M : ∀ i, GKModule Ad (V i)} (hM : ∀ i, (M i).IsAdmissible) :
    (GKModule.directSum M).IsAdmissible := by
  intro U hU
  have := fun i ↦ (hM i).finiteDimensional U.toRepresentation
  let c : IntertwiningMap U.toRepresentation (GKModule.directSum M).ρ →ₗ[k]
      ∀ i, IntertwiningMap U.toRepresentation (M i).ρ :=
    { toFun f i :=
        ⟨(DirectSum.component k ι V i).comp f.toLinearMap, fun g ↦ by
          ext w
          simp only [LinearMap.comp_apply, IntertwiningMap.toLinearMap_apply,
            IntertwiningMap.isIntertwining, ← DirectSum.apply_eq_component,
            GKModule.directSum_ρ_apply_apply]⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  refine Module.Finite.of_injective c fun f f' h ↦ ?_
  ext w i
  exact congr($h i w)

end IsAdmissible

/-- A finite-dimensional `(𝔤, K)`-module is admissible. -/
theorem isAdmissible_of_finiteDimensional [FiniteDimensional k V] : M.IsAdmissible :=
  IsAdmissible.of_finiteDimensional_isotypic M fun _ _ ↦ inferInstance

/-- A finite-dimensional `(𝔤, K)`-module is a Harish-Chandra module. -/
theorem isHarishChandraModule_of_finiteDimensional [FiniteDimensional k V] :
    M.IsHarishChandraModule := by
  classical
  refine ⟨M.isAdmissible_of_finiteDimensional, ?_⟩
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := k) (M := V)
  refine ⟨s, eq_top_iff.2 fun v _ ↦ ?_⟩
  exact LieSubmodule.submodule_span_le_lieSpan (hs ▸ Submodule.mem_top)

end GKModule

end TauCeti
