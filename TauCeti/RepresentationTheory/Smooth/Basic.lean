/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Pi.Basic
public import TauCeti.RepresentationTheory.Stabilizer
public import TauCeti.RepresentationTheory.Subrepresentation
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.Compact
import Mathlib.GroupTheory.GroupAction.Quotient
import TauCeti.RepresentationTheory.Invariants

/-!
# Smooth representations and smooth vectors

Let `G` be a topological group and `ρ` a representation of `G` on a module `V` over a semiring `A`,
with no topology on `V`. The representation is *smooth* when every vector has an open stabilizer.
For a locally profinite group, such as the rational points of a reductive group over a
nonarchimedean local field, this says that every vector is fixed by a compact open subgroup, and
these are the representations studied in the representation theory of `p`-adic groups.

Every representation has a largest smooth subrepresentation, its subrepresentation of *smooth
vectors* `V^∞`, made of the vectors with open stabilizer. When `G` is weakly locally compact and
nonarchimedean (locally profinite), `V^∞` is the union of the invariants `V^U` over the compact
open subgroups `U` of `G`.

## Main definitions

* `Representation.IsSmooth ρ`: every vector of `V` has an open stabilizer.
* `Representation.smoothVectors ρ`: the subrepresentation of vectors with open stabilizer.

## Main results

* `Representation.isSmooth_iff_exists_isCompact_openSubgroup`: for a locally profinite group, a
  representation is smooth when every vector is fixed by a compact open subgroup.
* `Representation.coe_smoothVectors_eq_iUnion`: for a locally profinite group, `V^∞` is the
  union of the invariants of the compact open subgroups.
* `Representation.le_smoothVectors_iff`: `V^∞` is the largest smooth subrepresentation.
* `Representation.smoothVectors_eq_top_iff`: `V^∞ = V` exactly when the representation is smooth.
* `Representation.IsSmooth.of_injective`, `Representation.IsSmooth.of_surjective`: smoothness
  passes to subrepresentations and quotients.
* `Representation.IsSmooth.comp`: smoothness passes to the restriction along a continuous
  homomorphism, in particular to subgroups.
* `Representation.isSmooth_ofMulAction_iff`: the permutation representation on `A[X]` is smooth
  exactly when every point of `X` has an open stabilizer, as for `X = G ⧸ U` with `U` open.
* `Representation.smoothVectors_leftRegular_eq_bot`: for a Hausdorff (indeed `T₁`) group that is
  not discrete, the left regular representation on `A[G]` has no nonzero smooth vector.

## References

* J. Bernstein, *Representations of p-adic groups*, Harvard lectures 1992, written by
  K. Rumelhart, Chapter I, §1.1, Definition 2 and Proposition 1, p. 7.
* JX-Mo, [mathlib4#41525](https://github.com/leanprover-community/mathlib4/pull/41525) (file
  `Mathlib/RepresentationTheory/Smooth/Basic.lean`), whose design this file follows:
  `IsSmooth` as a Prop-valued class asserting open stabilizers, and `smoothVectors` as a
  `Subrepresentation`.
-/

public section

open Set
open scoped MonoidAlgebra

namespace Representation

variable {A G V W : Type*} [Semiring A] [Group G]
  [AddCommMonoid V] [Module A V] [AddCommMonoid W] [Module A W]
  {ρ : Representation A G V} {σ : Representation A G W}

variable [TopologicalSpace G]

/-! ### Smooth representations -/

section IsSmooth

variable (ρ) in
/-- A representation of a topological group `G` is *smooth* when the stabilizer of every vector
is open in `G`. -/
@[mk_iff]
class IsSmooth : Prop where
  isOpen_stabilizer (v : V) : IsOpen (ρ.stabilizer v : Set G)

/-- A representation with an injective intertwining map to a smooth representation is smooth;
in particular smoothness passes to subrepresentations. -/
theorem IsSmooth.of_injective [IsSmooth σ] (f : ρ.IntertwiningMap σ)
    (hf : Function.Injective f) : IsSmooth ρ :=
  ⟨fun v ↦ f.stabilizer_apply_of_injective hf v ▸ IsSmooth.isOpen_stabilizer (f v)⟩

/-- A representation receiving a surjective intertwining map from a smooth representation is
smooth; in particular smoothness passes to quotients. -/
theorem IsSmooth.of_surjective [SeparatelyContinuousMul G] [IsSmooth ρ]
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f) : IsSmooth σ := by
  refine ⟨fun w ↦ ?_⟩
  obtain ⟨v, rfl⟩ := hf w
  exact Subgroup.isOpen_mono (f.stabilizer_le v) (IsSmooth.isOpen_stabilizer v)

/-- A subrepresentation of a smooth representation is smooth. -/
instance [IsSmooth ρ] (ρ' : Subrepresentation ρ) : IsSmooth ρ'.toRepresentation :=
  ⟨fun v ↦ ρ'.stabilizer_toRepresentation v ▸ IsSmooth.isOpen_stabilizer (v : V)⟩

/-- The restriction of a smooth representation along a continuous homomorphism is smooth. -/
theorem IsSmooth.comp [IsSmooth ρ] {H : Type*} [Group H] [TopologicalSpace H] {φ : H →* G}
    (hφ : Continuous φ) : IsSmooth (ρ.comp φ) :=
  ⟨fun v ↦ (IsSmooth.isOpen_stabilizer (ρ := ρ) v).preimage hφ⟩

/-- The restriction of a smooth representation to a subgroup is smooth. -/
instance [IsSmooth ρ] (H : Subgroup G) : IsSmooth (ρ.comp H.subtype) :=
  IsSmooth.comp continuous_subtypeVal

/-- Every representation of a discrete group is smooth. -/
instance [DiscreteTopology G] : IsSmooth ρ :=
  ⟨fun _ ↦ isOpen_discrete _⟩

/-- A trivial representation is smooth: every stabilizer is the whole group. -/
instance [ρ.IsTrivial] : IsSmooth ρ :=
  ⟨fun v ↦ by
    convert isOpen_univ
    exact Set.eq_univ_of_forall fun g ↦ by simp [IsTrivial.out (ρ := ρ) g]⟩

/-- The stabilizer of a vector in a smooth representation, bundled as an `OpenSubgroup G`. -/
def stabilizerOpenSubgroup (ρ : Representation A G V) [ρ.IsSmooth] (v : V) : OpenSubgroup G :=
  ⟨ρ.stabilizer v, IsSmooth.isOpen_stabilizer v⟩

@[simp]
theorem toSubgroup_stabilizerOpenSubgroup (ρ : Representation A G V) [ρ.IsSmooth] (v : V) :
    (ρ.stabilizerOpenSubgroup v).toSubgroup = ρ.stabilizer v :=
  (rfl)

@[simp]
theorem mem_stabilizerOpenSubgroup (ρ : Representation A G V) [ρ.IsSmooth] (v : V) {g : G} :
    g ∈ ρ.stabilizerOpenSubgroup v ↔ ρ g v = v :=
  Iff.rfl

/-- Every representation on a subsingleton module is smooth. -/
instance isSmooth_of_subsingleton [Subsingleton V] (ρ : Representation A G V) : ρ.IsSmooth :=
  ⟨fun v ↦ by
    have htop : (ρ.stabilizer v : Set G) = Set.univ :=
      Set.eq_univ_iff_forall.mpr fun _ ↦ Subsingleton.elim _ _
    rw [htop]
    exact isOpen_univ⟩

/-- Every smooth representation of a preconnected group with separately continuous multiplication
is trivial. -/
theorem isTrivial_of_isSmooth_of_preconnectedSpace [SeparatelyContinuousMul G]
    [PreconnectedSpace G] (ρ : Representation A G V) [ρ.IsSmooth] : ρ.IsTrivial :=
  ⟨fun g ↦ LinearMap.ext fun v ↦ by
    have htop : ρ.stabilizerOpenSubgroup v = ⊤ :=
      OpenSubgroup.eq_top_of_preconnectedSpace (ρ.stabilizerOpenSubgroup v)
    have hmem : g ∈ ρ.stabilizerOpenSubgroup v := htop.symm ▸ OpenSubgroup.mem_top g
    exact (mem_stabilizerOpenSubgroup ρ v).mp hmem⟩

/-- Equivalent representations are simultaneously smooth. -/
theorem Equiv.isSmooth_iff {ρ : Representation A G V} {σ : Representation A G W}
    (e : ρ.Equiv σ) : ρ.IsSmooth ↔ σ.IsSmooth :=
  ⟨fun _ ↦ IsSmooth.of_injective e.symm.toIntertwiningMap e.symm.injective,
    fun _ ↦ IsSmooth.of_injective e.toIntertwiningMap e.injective⟩

/-- The restriction of a smooth representation to an invariant submodule is smooth. -/
theorem IsSmooth.subrepresentation (ρ : Representation A G V) [ρ.IsSmooth] (U : Submodule A V)
    (hU : ∀ g, U ≤ U.comap (ρ g)) : (ρ.subrepresentation U hU).IsSmooth :=
  ⟨fun v ↦ by
    have hstab : (ρ.subrepresentation U hU).stabilizer v = ρ.stabilizer (v : V) := by
      ext g
      simp [mem_stabilizer, Subtype.ext_iff]
    rw [hstab]
    exact IsSmooth.isOpen_stabilizer (v : V)⟩

/-- The binary product of two smooth representations is smooth. -/
instance IsSmooth.prod (ρ : Representation A G V) (σ : Representation A G W)
    [ρ.IsSmooth] [σ.IsSmooth] : (ρ.prod σ).IsSmooth :=
  ⟨fun x ↦ by
    rw [stabilizer_prod, Subgroup.coe_inf]
    exact (IsSmooth.isOpen_stabilizer x.fst).inter (IsSmooth.isOpen_stabilizer x.snd)⟩

/-- A finite product of smooth representations is smooth. -/
instance IsSmooth.pi {ι : Type*} [Finite ι] {U : ι → Type*} [∀ i, AddCommMonoid (U i)]
    [∀ i, Module A (U i)] (ρ : ∀ i, Representation A G (U i)) [∀ i, (ρ i).IsSmooth] :
    (Representation.pi ρ).IsSmooth :=
  ⟨fun x ↦ by
    rw [stabilizer_pi, Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun i ↦ IsSmooth.isOpen_stabilizer (x i)⟩

/-- An arbitrary direct sum of smooth representations is smooth. -/
instance IsSmooth.directSum {ι : Type*} {U : ι → Type*} [∀ i, AddCommMonoid (U i)]
    [∀ i, Module A (U i)] (ρ : ∀ i, Representation A G (U i)) [∀ i, (ρ i).IsSmooth] :
    (Representation.directSum ρ).IsSmooth :=
  ⟨fun x ↦ by
    classical
    have hstab : ((Representation.directSum ρ).stabilizer x : Set G) =
        ⋂ i ∈ x.support, ((ρ i).stabilizer (x i) : Set G) := by
      ext g
      simp only [SetLike.mem_coe, mem_stabilizer, Set.mem_iInter, DFinsupp.mem_support_toFun,
        directSum_apply, DirectSum.ext_iff, DirectSum.lmap_apply]
      refine ⟨fun h i _ ↦ h i, fun h i ↦ ?_⟩
      by_cases hi : x i = 0
      · simp [hi]
      · exact h i hi
    rw [hstab]
    exact isOpen_biInter_finset fun i _ ↦ IsSmooth.isOpen_stabilizer (x i)⟩

end IsSmooth

/-! ### The subrepresentation of smooth vectors -/

section SmoothVectors

variable [SeparatelyContinuousMul G]

variable (ρ) in
/-- The *smooth vectors* `V^∞` of a representation of a topological group: the vectors whose
stabilizer is open. It is the largest smooth subrepresentation (`le_smoothVectors_iff`). -/
def smoothVectors : Subrepresentation ρ where
  toSubmodule :=
    { carrier := {v | IsOpen (ρ.stabilizer v : Set G)}
      add_mem' := fun {v w} hv hw ↦
        Subgroup.isOpen_mono (ρ.le_stabilizer_add v w) (hv.inter hw)
      zero_mem' := by simp [stabilizer_zero]
      smul_mem' := fun c v hv ↦ Subgroup.isOpen_mono (ρ.le_stabilizer_smul c v) hv }
  apply_mem_toSubmodule g v hv := by
    -- The stabilizer of `ρ g v` is the image of that of `v` under `x ↦ g * x * g⁻¹`.
    -- `mem_smoothVectors_iff` is not available inside this definition, so `change` unfolds
    -- membership in the carrier above.
    change IsOpen (ρ.stabilizer v : Set G) at hv
    change IsOpen (ρ.stabilizer (ρ g v) : Set G)
    have himage : (((ρ.stabilizer v).map (MulAut.conj g) : Subgroup G) : Set G) =
        (Homeomorph.mulLeft g).trans (Homeomorph.mulRight g⁻¹) '' ρ.stabilizer v := by
      ext
      simp [MulAut.conj_apply]
    rw [stabilizer_conj, himage]
    exact ((Homeomorph.mulLeft g).trans (Homeomorph.mulRight g⁻¹)).isOpenMap _ hv

@[simp]
theorem mem_smoothVectors_iff {v : V} :
    v ∈ ρ.smoothVectors ↔ IsOpen (ρ.stabilizer v : Set G) :=
  Iff.rfl

/-- A vector lies in `V^∞` exactly when it is fixed by an open subgroup. -/
theorem mem_smoothVectors_iff_exists_openSubgroup {v : V} :
    v ∈ ρ.smoothVectors ↔ ∃ U : OpenSubgroup G, (U : Subgroup G) ≤ ρ.stabilizer v :=
  ⟨fun hv ↦ ⟨⟨ρ.stabilizer v, hv⟩, le_rfl⟩, fun ⟨_, hU⟩ ↦ Subgroup.isOpen_of_openSubgroup _ hU⟩

/-- For a locally profinite group, a vector lies in `V^∞` exactly when it is fixed by a compact
open subgroup. -/
theorem mem_smoothVectors_iff_exists_isCompact_openSubgroup [NonarchimedeanGroup G]
    [WeaklyLocallyCompactSpace G] {v : V} :
    v ∈ ρ.smoothVectors ↔
      ∃ U : OpenSubgroup G, IsCompact (U : Set G) ∧ (U : Subgroup G) ≤ ρ.stabilizer v :=
  (ρ.stabilizer v).isOpen_iff_exists_isCompact_openSubgroup_le

/-- Translates of smooth vectors are smooth. -/
theorem apply_mem_smoothVectors {v : V} (hv : v ∈ ρ.smoothVectors) (g : G) :
    ρ g v ∈ ρ.smoothVectors :=
  ρ.smoothVectors.apply_mem_toSubmodule g hv

/-- Intertwining maps send smooth vectors to smooth vectors. -/
theorem IntertwiningMap.apply_mem_smoothVectors (f : ρ.IntertwiningMap σ) {v : V}
    (hv : v ∈ ρ.smoothVectors) : f v ∈ σ.smoothVectors :=
  Subgroup.isOpen_mono (f.stabilizer_le v) hv

/-- A representation is smooth exactly when every vector is smooth. -/
theorem isSmooth_iff_forall_mem_smoothVectors : IsSmooth ρ ↔ ∀ v, v ∈ ρ.smoothVectors :=
  isSmooth_iff ρ

/-- Every vector of a smooth representation is smooth. -/
theorem IsSmooth.mem_smoothVectors [IsSmooth ρ] (v : V) : v ∈ ρ.smoothVectors :=
  IsSmooth.isOpen_stabilizer v

/-- A representation is smooth exactly when every vector is fixed by an open subgroup. -/
theorem isSmooth_iff_exists_openSubgroup :
    IsSmooth ρ ↔ ∀ v, ∃ U : OpenSubgroup G, (U : Subgroup G) ≤ ρ.stabilizer v := by
  simp only [isSmooth_iff_forall_mem_smoothVectors, mem_smoothVectors_iff_exists_openSubgroup]

/-- For a locally profinite group, a representation is smooth exactly when every vector is fixed
by a compact open subgroup. -/
theorem isSmooth_iff_exists_isCompact_openSubgroup [NonarchimedeanGroup G]
    [WeaklyLocallyCompactSpace G] :
    IsSmooth ρ ↔
      ∀ v, ∃ U : OpenSubgroup G, IsCompact (U : Set G) ∧ (U : Subgroup G) ≤ ρ.stabilizer v := by
  simp only [isSmooth_iff_forall_mem_smoothVectors,
    mem_smoothVectors_iff_exists_isCompact_openSubgroup]

/-- `V^∞` is smooth. -/
instance : IsSmooth ρ.smoothVectors.toRepresentation :=
  ⟨fun v ↦ ρ.smoothVectors.stabilizer_toRepresentation v ▸ v.property⟩

/-- `V^∞` is the largest smooth subrepresentation: a subrepresentation lies in it exactly when it
is smooth. -/
theorem le_smoothVectors_iff {ρ' : Subrepresentation ρ} :
    ρ' ≤ ρ.smoothVectors ↔ IsSmooth ρ'.toRepresentation := by
  rw [isSmooth_iff]
  refine ⟨fun h v ↦ ?_, fun h v hv ↦ ?_⟩
  · rw [Subrepresentation.stabilizer_toRepresentation]
    exact h v.property
  · simpa using h ⟨v, hv⟩

/-- `V^∞ = V` exactly when the representation is smooth. -/
theorem smoothVectors_eq_top_iff : ρ.smoothVectors = ⊤ ↔ IsSmooth ρ := by
  rw [eq_top_iff, isSmooth_iff_forall_mem_smoothVectors]
  refine ⟨fun h v ↦ h ?_, fun h v _ ↦ h v⟩
  rw [← Subrepresentation.mem_toSubmodule, Subrepresentation.toSubmodule_top]
  exact Submodule.mem_top

/-- A smooth representation is its own subrepresentation of smooth vectors. -/
@[simp]
theorem smoothVectors_eq_top [IsSmooth ρ] : ρ.smoothVectors = ⊤ :=
  smoothVectors_eq_top_iff.2 inferInstance

/-- An injective intertwining map detects smooth vectors. -/
theorem IntertwiningMap.apply_mem_smoothVectors_iff_of_injective (f : ρ.IntertwiningMap σ)
    (hf : Function.Injective f) {v : V} : f v ∈ σ.smoothVectors ↔ v ∈ ρ.smoothVectors := by
  rw [mem_smoothVectors_iff, mem_smoothVectors_iff, f.stabilizer_apply_of_injective hf v]

/-- Any intertwining map from a smooth representation `ρ` into `σ` factors through the
subrepresentation of smooth vectors `σ.smoothVectors`. -/
def IntertwiningMap.liftSmoothVectors [IsSmooth ρ] (f : ρ.IntertwiningMap σ) :
    ρ.IntertwiningMap σ.smoothVectors.toRepresentation :=
  f.codRestrict σ.smoothVectors fun v ↦
    Subrepresentation.mem_toSubmodule.mpr (f.apply_mem_smoothVectors (IsSmooth.isOpen_stabilizer v))

@[simp]
theorem IntertwiningMap.coe_liftSmoothVectors_apply [IsSmooth ρ] (f : ρ.IntertwiningMap σ)
    (v : V) : (f.liftSmoothVectors v : W) = f v :=
  f.codRestrict_apply_coe σ.smoothVectors _ v

@[simp]
theorem IntertwiningMap.subtype_comp_liftSmoothVectors [IsSmooth ρ] (f : ρ.IntertwiningMap σ) :
    σ.smoothVectors.subtype.comp f.liftSmoothVectors = f := by
  ext v
  simp

/-- **Universal property of `smoothVectors`**: an intertwining map `ρ → σ.smoothVectors` from a
smooth representation `ρ` equals `f.liftSmoothVectors` iff composing with the inclusion recovers
`f`. -/
theorem IntertwiningMap.eq_liftSmoothVectors_iff [IsSmooth ρ] {f : ρ.IntertwiningMap σ}
    {g : ρ.IntertwiningMap σ.smoothVectors.toRepresentation} :
    g = f.liftSmoothVectors ↔ σ.smoothVectors.subtype.comp g = f := by
  refine ⟨fun h ↦ h ▸ subtype_comp_liftSmoothVectors f, fun h ↦ ?_⟩
  ext v
  have h' := congrArg (fun φ : ρ.IntertwiningMap σ ↦ φ v) h
  simpa using h'

/-- An intertwining map `f : ρ → σ` restricts to an intertwining map between the smooth-vector
subrepresentations. -/
def IntertwiningMap.restrictSmoothVectors (f : ρ.IntertwiningMap σ) :
    ρ.smoothVectors.toRepresentation.IntertwiningMap σ.smoothVectors.toRepresentation :=
  (f.comp ρ.smoothVectors.subtype).liftSmoothVectors

@[simp]
theorem IntertwiningMap.coe_restrictSmoothVectors_apply (f : ρ.IntertwiningMap σ)
    (v : ρ.smoothVectors.toSubmodule) : (f.restrictSmoothVectors v : W) = f v := by
  simp [restrictSmoothVectors]

@[simp]
theorem IntertwiningMap.restrictSmoothVectors_id (ρ : Representation A G V) :
    (IntertwiningMap.id ρ).restrictSmoothVectors =
      IntertwiningMap.id ρ.smoothVectors.toRepresentation := by
  ext v
  simp

@[simp]
theorem IntertwiningMap.restrictSmoothVectors_comp {U : Type*} [AddCommMonoid U] [Module A U]
    {τ : Representation A G U} (g : σ.IntertwiningMap τ) (f : ρ.IntertwiningMap σ) :
    (g.comp f).restrictSmoothVectors = g.restrictSmoothVectors.comp f.restrictSmoothVectors := by
  ext v
  simp

@[simp]
theorem IntertwiningMap.subtype_comp_restrictSmoothVectors (f : ρ.IntertwiningMap σ) :
    σ.smoothVectors.subtype.comp f.restrictSmoothVectors = f.comp ρ.smoothVectors.subtype := by
  ext v
  simp

/-- A pair `(v, w)` is a smooth vector of `ρ.prod σ` iff both `v` and `w` are smooth vectors. -/
theorem mem_smoothVectors_prod_iff {x : V × W} :
    x ∈ (ρ.prod σ).smoothVectors ↔ x.fst ∈ ρ.smoothVectors ∧ x.snd ∈ σ.smoothVectors := by
  simp only [mem_smoothVectors_iff, stabilizer_prod, Subgroup.coe_inf]
  refine ⟨fun h ↦ ⟨Subgroup.isOpen_mono inf_le_left h, Subgroup.isOpen_mono inf_le_right h⟩,
    fun ⟨h₁, h₂⟩ ↦ h₁.inter h₂⟩

/-- A smooth vector of `ρ` remains smooth after restriction along a continuous group
homomorphism. -/
theorem smoothVectors_toSubmodule_le_comp {H : Type*} [Group H] [TopologicalSpace H]
    [SeparatelyContinuousMul H] (ρ : Representation A G V) {f : H →* G} (hf : Continuous f) :
    ρ.smoothVectors.toSubmodule ≤ (smoothVectors (ρ.comp f)).toSubmodule := by
  intro v hv
  rw [Subrepresentation.mem_toSubmodule, mem_smoothVectors_iff, stabilizer_comp, Subgroup.coe_comap]
  exact hv.preimage hf

end SmoothVectors

/-! ### Invariants of open and compact open subgroups -/

section Invariants

variable {A G V : Type*} [CommRing A] [Group G] [AddCommGroup V] [Module A V]
  {ρ : Representation A G V} [TopologicalSpace G]

/-- The underlying submodule of `ρ.smoothVectors` is the directed supremum of the open-subgroup
invariant submodules `invariants (ρ.comp U.toSubgroup.subtype)`. -/
theorem smoothVectors_toSubmodule_eq_iSup [SeparatelyContinuousMul G]
    (ρ : Representation A G V) :
    ρ.smoothVectors.toSubmodule =
      ⨆ U : OpenSubgroup G, invariants (ρ.comp (U : Subgroup G).subtype) := by
  have hdir : Directed (· ≤ ·)
      (fun U : OpenSubgroup G ↦ invariants (ρ.comp (U : Subgroup G).subtype)) :=
    fun U₁ U₂ ↦ ⟨U₁ ⊓ U₂,
      invariants_comp_subtype_antitone ρ (inf_le_left : (U₁ ⊓ U₂ : Subgroup G) ≤ U₁),
      invariants_comp_subtype_antitone ρ (inf_le_right : (U₁ ⊓ U₂ : Subgroup G) ≤ U₂)⟩
  ext v
  rw [Subrepresentation.mem_toSubmodule, mem_smoothVectors_iff_exists_openSubgroup,
    Submodule.mem_iSup_of_directed _ hdir]
  simp only [mem_invariants_comp_subtype_iff]

/-- A representation is smooth iff `V` is the supremum of its open-subgroup invariant submodules. -/
theorem isSmooth_iff_iSup_invariants_eq_top [SeparatelyContinuousMul G]
    (ρ : Representation A G V) :
    ρ.IsSmooth ↔ (⨆ U : OpenSubgroup G, invariants (ρ.comp (U : Subgroup G).subtype)) = ⊤ := by
  rw [← smoothVectors_toSubmodule_eq_iSup, ← Subrepresentation.toSubmodule_top (ρ := ρ),
    Subrepresentation.toSubmodule_injective.eq_iff, smoothVectors_eq_top_iff]

variable [NonarchimedeanGroup G] [WeaklyLocallyCompactSpace G]

/-- For a locally profinite group, `V^∞ = ⋃ V^U`, the union of the invariants of the compact open
subgroups `U`. -/
theorem coe_smoothVectors_eq_iUnion :
    (ρ.smoothVectors : Set V) =
      ⋃ (U : OpenSubgroup G) (_ : IsCompact (U : Set G)),
        (invariants (ρ.comp (U : Subgroup G).subtype) : Set V) := by
  ext v
  simp only [SetLike.mem_coe, mem_smoothVectors_iff_exists_isCompact_openSubgroup, mem_iUnion,
    mem_invariants_comp_subtype_iff, exists_prop]

/-- For a locally profinite group, a representation is smooth exactly when `V = ⋃ V^U`, the
union of the invariants of the compact open subgroups `U`. -/
theorem isSmooth_iff_iUnion_eq_univ :
    IsSmooth ρ ↔
      ⋃ (U : OpenSubgroup G) (_ : IsCompact (U : Set G)),
        (invariants (ρ.comp (U : Subgroup G).subtype) : Set V) = univ := by
  simp only [← coe_smoothVectors_eq_iUnion, isSmooth_iff_forall_mem_smoothVectors,
    eq_univ_iff_forall, SetLike.mem_coe]

/-- For a locally profinite group, the underlying submodule of `ρ.smoothVectors` is the directed
supremum of the compact-open-subgroup invariant submodules. -/
theorem smoothVectors_toSubmodule_eq_iSup_isCompact (ρ : Representation A G V) :
    ρ.smoothVectors.toSubmodule =
      ⨆ (U : OpenSubgroup G) (_ : IsCompact (U : Set G)),
        invariants (ρ.comp (U : Subgroup G).subtype) := by
  obtain ⟨K₀, hK₀, -⟩ :=
    (NonarchimedeanGroup.nhds_one_hasBasis_isCompact_openSubgroup (G := G)).mem_iff.1
      Filter.univ_mem
  have : Nonempty {U : OpenSubgroup G // IsCompact (U : Set G)} := ⟨⟨K₀, hK₀⟩⟩
  have hdir : Directed (· ≤ ·) (fun U : {U : OpenSubgroup G // IsCompact (U : Set G)} ↦
      invariants (ρ.comp (U : Subgroup G).subtype)) :=
    fun U₁ U₂ ↦ by
      obtain ⟨U, hUc, hU₁, hU₂⟩ := OpenSubgroup.directedOn_isCompact U₁.val U₁.property U₂.val
        U₂.property
      exact ⟨⟨U, hUc⟩, invariants_comp_subtype_antitone ρ hU₁,
        invariants_comp_subtype_antitone ρ hU₂⟩
  ext v
  rw [Subrepresentation.mem_toSubmodule, mem_smoothVectors_iff_exists_isCompact_openSubgroup,
    iSup_subtype', Submodule.mem_iSup_of_directed _ hdir]
  simp only [mem_invariants_comp_subtype_iff, Subtype.exists, exists_prop]

/-- For a locally profinite group, a representation is smooth iff `V` is the supremum of its
compact-open-subgroup invariant submodules. -/
theorem isSmooth_iff_iSup_isCompact_invariants_eq_top (ρ : Representation A G V) :
    ρ.IsSmooth ↔
      (⨆ (U : OpenSubgroup G) (_ : IsCompact (U : Set G)),
        invariants (ρ.comp (U : Subgroup G).subtype)) = ⊤ := by
  rw [← smoothVectors_toSubmodule_eq_iSup_isCompact, ← Subrepresentation.toSubmodule_top (ρ := ρ),
    Subrepresentation.toSubmodule_injective.eq_iff, smoothVectors_eq_top_iff]

end Invariants

/-! ### Quotients and tensor products -/

section Quotient

variable {A G V : Type*} [Ring A] [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
  [AddCommGroup V] [Module A V] {ρ : Representation A G V}

/-- A quotient of a smooth representation by an invariant submodule is smooth. -/
instance [IsSmooth ρ] (W : Submodule A V) (le_comap : ∀ g, W ≤ W.comap (ρ g)) :
    IsSmooth (ρ.quotient W le_comap) :=
  IsSmooth.of_surjective (σ := ρ.quotient W le_comap)
    ⟨W.mkQ, fun _ ↦ rfl⟩ W.mkQ_surjective

/-- The quotient of a smooth representation by a subrepresentation is smooth. -/
instance [IsSmooth ρ] (ρ' : Subrepresentation ρ) : IsSmooth ρ'.quotient :=
  inferInstanceAs (IsSmooth (ρ.quotient _ _))

end Quotient

section Tensor

variable {A G V W : Type*} [CommSemiring A] [Group G] [TopologicalSpace G]
  [SeparatelyContinuousMul G] [AddCommMonoid V] [Module A V] [AddCommMonoid W] [Module A W]

/-- The tensor product of two smooth representations over a commutative semiring is smooth. -/
instance IsSmooth.tprod (ρ : Representation A G V) (σ : Representation A G W)
    [ρ.IsSmooth] [σ.IsSmooth] : (ρ.tprod σ).IsSmooth :=
  ⟨fun z ↦ by
    induction z using TensorProduct.inductionOn with
    | tmul v w =>
      have hle : ρ.stabilizer v ⊓ σ.stabilizer w ≤ (ρ.tprod σ).stabilizer (v ⊗ₜ[A] w) := by
        intro g hg
        simp only [mem_stabilizer, tprod_apply, TensorProduct.map_tmul]
        rw [hg.left, hg.right]
      exact Subgroup.isOpen_mono hle
        ((IsSmooth.isOpen_stabilizer v).inter (IsSmooth.isOpen_stabilizer w))
    | add x y hx hy =>
      exact Subgroup.isOpen_mono (le_stabilizer_add (ρ.tprod σ) x y) (hx.inter hy)⟩

end Tensor

/-! ### Permutation representations -/

section OfMulAction

variable {X : Type*} [MulAction G X]

/-- The permutation representation on `A[X]` is smooth when every point of `X` has an open
stabilizer. -/
theorem isSmooth_ofMulAction [SeparatelyContinuousMul G]
    (h : ∀ x : X, IsOpen (MulAction.stabilizer G x : Set G)) : IsSmooth (ofMulAction A G X) := by
  rw [isSmooth_iff_forall_mem_smoothVectors]
  intro f
  induction f using MonoidAlgebra.induction_linear with
  | zero => exact (ofMulAction A G X).smoothVectors.toSubmodule.zero_mem
  | add f₁ f₂ h₁ h₂ => exact (ofMulAction A G X).smoothVectors.toSubmodule.add_mem h₁ h₂
  | single x r =>
    refine Subgroup.isOpen_mono (fun g hg ↦ ?_) (h x)
    rw [mem_stabilizer, ofMulAction_single, MulAction.mem_stabilizer_iff.1 hg]

/-- Over a nontrivial semiring, the permutation representation on `A[X]` is smooth exactly when
every point of `X` has an open stabilizer. -/
theorem isSmooth_ofMulAction_iff [SeparatelyContinuousMul G] [Nontrivial A] :
    IsSmooth (ofMulAction A G X) ↔ ∀ x : X, IsOpen (MulAction.stabilizer G x : Set G) :=
  ⟨fun _ x ↦ stabilizer_ofMulAction_single (A := A) (G := G) x one_ne_zero ▸
    IsSmooth.isOpen_stabilizer _, isSmooth_ofMulAction⟩

/-- The permutation representation on a discrete set with a continuous action is smooth; for
instance `A[G ⧸ U]` for an open subgroup `U`. -/
instance [SeparatelyContinuousMul G] [TopologicalSpace X] [DiscreteTopology X]
    [ContinuousSMul G X] : IsSmooth (ofMulAction A G X) :=
  isSmooth_ofMulAction (stabilizer_isOpen G)

/-- The coset permutation representation `ofMulAction A G (G ⧸ H)` is smooth whenever `H` is an
open subgroup of `G`. -/
theorem isSmooth_ofMulAction_quotient [SeparatelyContinuousMul G] {H : Subgroup G}
    (hH : IsOpen (H : Set G)) : (ofMulAction A G (G ⧸ H)).IsSmooth := by
  refine isSmooth_ofMulAction fun q ↦ ?_
  induction q using QuotientGroup.induction_on with
  | H g =>
    have hpre : (MulAction.stabilizer G (g : G ⧸ H) : Set G) =
        (fun x ↦ g⁻¹ * x * g) ⁻¹' (H : Set G) := by
      ext x
      simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Set.mem_preimage]
      have hsmul : x • (g : G ⧸ H) = ((x * g : G) : G ⧸ H) := rfl
      rw [hsmul, QuotientGroup.eq, mul_inv_rev, mul_assoc]
      exact ⟨fun h ↦ by simpa [mul_assoc] using H.inv_mem h,
        fun h ↦ by simpa [mul_assoc] using H.inv_mem h⟩
    rw [hpre]
    exact hH.preimage ((Homeomorph.mulRight g).continuous.comp (Homeomorph.mulLeft g⁻¹).continuous)

/-- Over a nontrivial coefficient semiring, the coset permutation representation on `A[G ⧸ H]` is
smooth iff `H` is open in `G`. -/
theorem isSmooth_ofMulAction_quotient_iff [SeparatelyContinuousMul G] [Nontrivial A]
    (H : Subgroup G) : (ofMulAction A G (G ⧸ H)).IsSmooth ↔ IsOpen (H : Set G) := by
  refine ⟨fun h ↦ ?_, isSmooth_ofMulAction_quotient⟩
  have h1 := (isSmooth_ofMulAction_iff (A := A) (G := G)).mp h ((1 : G) : G ⧸ H)
  rwa [MulAction.stabilizer_quotient] at h1

/-- A product of coset permutation representations `∏ i, A[G ⧸ H i]` is not smooth whenever the
intersection `⨅ i, H i` is not open (in particular, an infinite product of smooth representations
need not be smooth). -/
theorem not_isSmooth_pi_ofMulAction_quotient [Nontrivial A] {ι : Type*}
    (H : ι → Subgroup G) (hH : ¬ IsOpen ((⨅ i, H i : Subgroup G) : Set G)) :
    ¬ (Representation.pi fun i ↦ ofMulAction A G (G ⧸ H i)).IsSmooth := by
  intro h
  apply hH
  have hstab : (Representation.pi fun i ↦ ofMulAction A G (G ⧸ H i)).stabilizer
      (fun i ↦ MonoidAlgebra.single ((1 : G) : G ⧸ H i) (1 : A)) = ⨅ i, H i := by
    rw [stabilizer_pi]
    congr 1
    ext i
    rw [stabilizer_ofMulAction_single _ one_ne_zero, MulAction.stabilizer_quotient]
  rw [← hstab]
  exact h.isOpen_stabilizer _

/-- Over a nontrivial semiring, the left regular representation on `A[G]` is smooth exactly when
`G` is discrete. -/
theorem isSmooth_leftRegular_iff [SeparatelyContinuousMul G] [Nontrivial A] :
    IsSmooth (leftRegular A G) ↔ DiscreteTopology G := by
  simp [isSmooth_ofMulAction_iff, discreteTopology_iff_isOpen_singleton_one]

/-- For a `T₁` group that is not discrete, the left regular representation on `A[G]` has no
nonzero smooth vector. -/
theorem smoothVectors_leftRegular_eq_bot [SeparatelyContinuousMul G] [T1Space G]
    (hG : ¬ DiscreteTopology G) : (leftRegular A G).smoothVectors = ⊥ := by
  -- A nonzero `f` with open stabilizer `H` would make `H` finite, since `H` permutes the finite
  -- support of `f`, and a finite open subgroup of a `T₁` group makes `{1}` open.
  refine eq_bot_iff.2 fun f hf ↦ ?_
  rw [← Subrepresentation.mem_toSubmodule, Subrepresentation.toSubmodule_bot, Submodule.mem_bot]
  by_contra hf0
  obtain ⟨x, hx⟩ := Finsupp.support_nonempty_iff.2 (mt MonoidAlgebra.coeff_eq_zero.1 hf0)
  set H := (leftRegular A G).stabilizer f
  -- Every `g ∈ H` sends `x` into the support of `f`, so `H` lies in a finite set.
  have hfin : (H : Set G).Finite := by
    refine ((f.coeff.support.finite_toSet.image fun y ↦ y * x⁻¹)).subset fun g hg ↦ ?_
    refine ⟨g * x, ?_, by simp⟩
    rw [← mem_stabilizer.1 hg]
    simpa [coeff_ofMulAction] using hx
  exact hG (discreteTopology_of_isOpen_singleton_one
    (isOpen_singleton_of_finite_mem_nhds 1 ((mem_smoothVectors_iff.1 hf).mem_nhds H.one_mem) hfin))

end OfMulAction

end Representation
