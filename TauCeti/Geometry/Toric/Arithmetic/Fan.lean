/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Compactness.Compact
public import TauCeti.Geometry.Toric.Algebraic.Fan.Basic

/-!
# Arithmetic cone systems

The boundary charts of a toroidal compactification of a locally symmetric variety are toric
charts, but the cone decomposition they come from is not a finite fan. At a cusp one has a
lattice `i : N →+ V`, an open positivity cone `C ⊆ V`, its rational closure `C*` with
`C ⊆ C*`, and an arithmetic group `Γ` acting linearly on `V`. The relevant decompositions are
possibly infinite collections of toric cones inside `C*`, stable under `Γ`, with only finitely
many cones modulo `Γ`, and locally finite on the open cone `C`. These are Pink's admissible
partial cone decompositions at one cusp, Ash–Mumford–Rapoport–Tai's admissible polyhedral
decompositions, and Dimitrov's fans at a Hilbert cusp.

The arithmetic group enters through its image `Γ` in the linear automorphisms of `V`: it acts on
cones through its effective quotient. The arithmetic group of the boundary datum preserves the
lattice and the cone `C*`; none of the statements here needs this, so it is not a field.

Two finiteness conditions replace the finiteness of a fan. Finitely many orbits does not mean
finitely many cones: for a Hilbert cusp of degree greater than one, the unit group has infinite
orbits. Local finiteness is required on compact subsets of `C` only, never at the origin. Every
cone contains `0`, so a system that is locally finite near `0` is finite
(`TauCeti.Toric.ArithmeticFan.finite_cones_of_zero_mem`).

## Main declarations

* `TauCeti.Toric.ArithmeticFan`: a `Γ`-stable, locally finite system of toric cones in `C*`
  with finitely many `Γ`-orbits, any two of which meet in a common face.
* `TauCeti.Toric.ArithmeticFan.support` and `TauCeti.Toric.ArithmeticFan.IsComplete`: the union
  of the cones, and the condition that it is all of `C*` (not of the ambient space).
* `TauCeti.Toric.ArithmeticFan.image_support`: the support is `Γ`-invariant.
* `TauCeti.Toric.ArithmeticFan.toFiniteFan`: a system with finitely many cones is a finite `Fan`
  with the same cones, and `TauCeti.Toric.Fan.toArithmeticFan` is the converse construction for a
  `Γ`-stable finite fan.
* `TauCeti.Toric.ArithmeticFan.restrict`: the same cones as a system for a subgroup of finite
  index, the change to a smaller level.
* `TauCeti.Toric.ArithmeticFan.bot`: the system consisting of the zero cone alone, which is
  complete exactly when `C* = {0}`; conversely, when `C* = {0}` every complete system is this one
  (`TauCeti.Toric.ArithmeticFan.IsComplete.cones_eq_singleton_bot`).

## References

* R. Pink, *Arithmetical compactification of mixed Shimura varieties*, Bonner Math. Schriften
  209 (1990), §§6.4–6.6.
* A. Ash, D. Mumford, M. Rapoport and Y.-S. Tai, *Smooth compactifications of locally symmetric
  varieties*, Chapter II.
* M. Dimitrov, *Compactifications arithmétiques des variétés de Hilbert et formes modulaires de
  Hilbert pour Γ₁(c, n)*, Définition 7.1.
-/

public section

namespace TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  {i : N →+ V}

/-- An *arithmetic cone system* (Pink's admissible partial cone decomposition at one cusp) for
the lattice `i : N →+ V`, the group `Γ` of linear automorphisms of `V`, the open positivity cone
`C` and its rational closure `Cstar`. It is a possibly infinite set of toric cones contained in
`Cstar`, closed under passing to faces, any two of which meet in a face of each, stable under
`Γ`, with finitely many `Γ`-orbits, and locally finite on compact subsets of `C`. The topology
on `V` is a Hausdorff topological vector space topology; since `V` is finite-dimensional by
`IsIntegralLattice`, it is the Euclidean topology. -/
structure ArithmeticFan [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V] (i : N →+ V)
    (Γ : Subgroup (V ≃ₗ[ℝ] V)) (C Cstar : Set V) where
  /-- The ambient map of integral vectors is an integral lattice. -/
  lattice : IsIntegralLattice i
  /-- The cones of the system. -/
  cones : Set (PointedCone ℝ V)
  /-- Every cone of the system is a toric cone. -/
  isToricCone : ∀ ⦃σ⦄, σ ∈ cones → IsToricCone i σ
  /-- Every cone of the system lies in the rational closure of the positivity cone. -/
  coe_subset : ∀ ⦃σ⦄, σ ∈ cones → (σ : Set V) ⊆ Cstar
  /-- The cones of the system are closed under passing to faces. -/
  mem_of_isFaceOf : ∀ ⦃σ τ⦄, σ ∈ cones → τ.IsFaceOf σ → τ ∈ cones
  /-- The intersection of two cones of the system is a face of the first one; exchanging the
  cones gives the same statement for the second one. -/
  inf_isFaceOf_left : ∀ ⦃σ τ⦄, σ ∈ cones → τ ∈ cones → (σ ⊓ τ).IsFaceOf σ
  /-- The group `Γ` permutes the cones of the system. -/
  map_mem : ∀ ⦃g⦄, g ∈ Γ → ∀ ⦃σ⦄, σ ∈ cones → σ.map (g : V →ₗ[ℝ] V) ∈ cones
  /-- The system has finitely many `Γ`-orbits of cones. -/
  exists_finite_orbit_representatives : ∃ S : Set (PointedCone ℝ V), S.Finite ∧
    ∀ σ ∈ cones, ∃ τ ∈ S, ∃ g ∈ Γ, τ.map (g : V →ₗ[ℝ] V) = σ
  /-- Only finitely many cones of the system meet a compact subset of the positivity cone. -/
  finite_setOf_inter_nonempty : ∀ ⦃K : Set V⦄, IsCompact K → K ⊆ C →
    {σ | σ ∈ cones ∧ ((σ : Set V) ∩ K).Nonempty}.Finite

variable [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]

namespace ArithmeticFan

variable {Γ : Subgroup (V ≃ₗ[ℝ] V)} {C Cstar : Set V} (Φ : ArithmeticFan i Γ C Cstar)
  {σ τ : PointedCone ℝ V}

/-- An arithmetic cone system is determined by its set of cones. -/
@[ext]
theorem ext {Φ Ψ : ArithmeticFan i Γ C Cstar} (h : Φ.cones = Ψ.cones) : Φ = Ψ := by
  cases Φ
  cases Ψ
  cases h
  rfl

/-! ### Incidence -/

/-- The intersection of two cones of an arithmetic cone system is a face of the second one. -/
theorem inf_isFaceOf_right (hσ : σ ∈ Φ.cones) (hτ : τ ∈ Φ.cones) : (σ ⊓ τ).IsFaceOf τ :=
  inf_comm σ τ ▸ Φ.inf_isFaceOf_left hτ hσ

/-- The intersection of two cones of an arithmetic cone system is again one of its cones. -/
theorem inf_mem (hσ : σ ∈ Φ.cones) (hτ : τ ∈ Φ.cones) : σ ⊓ τ ∈ Φ.cones :=
  Φ.mem_of_isFaceOf hσ (Φ.inf_isFaceOf_left hσ hτ)

/-- A nonempty arithmetic cone system contains the zero cone. -/
theorem bot_mem (hσ : σ ∈ Φ.cones) : (⊥ : PointedCone ℝ V) ∈ Φ.cones :=
  Φ.mem_of_isFaceOf hσ (Φ.isToricCone hσ).salient.bot_isFaceOf

/-- A cone belongs to the system exactly when one of its `Γ`-translates does. -/
@[simp]
theorem map_mem_iff {g : V ≃ₗ[ℝ] V} (hg : g ∈ Γ) :
    σ.map (g : V →ₗ[ℝ] V) ∈ Φ.cones ↔ σ ∈ Φ.cones := by
  refine ⟨fun h ↦ ?_, fun h ↦ Φ.map_mem hg h⟩
  have h' := Φ.map_mem (inv_mem hg) h
  rwa [← PointedCone.map_linearEquiv_mul, inv_mul_cancel, LinearEquiv.coe_toLinearMap_one,
    PointedCone.map_id] at h'

/-! ### Local finiteness -/

/-- Only finitely many cones of an arithmetic cone system contain a given point of the
positivity cone. -/
theorem finite_setOf_mem {x : V} (hx : x ∈ C) : {σ | σ ∈ Φ.cones ∧ x ∈ σ}.Finite := by
  refine (Φ.finite_setOf_inter_nonempty isCompact_singleton
    (Set.singleton_subset_iff.2 hx)).subset fun σ hσ ↦ ⟨hσ.1, x, hσ.2, rfl⟩

/-- An arithmetic cone system whose positivity cone contains the origin has only finitely many
cones, since every cone contains the origin. Infinite systems are therefore locally finite only
away from the origin. -/
theorem finite_cones_of_zero_mem (h0 : (0 : V) ∈ C) : Φ.cones.Finite :=
  (Φ.finite_setOf_mem h0).subset fun σ hσ ↦ ⟨hσ, σ.zero_mem⟩

/-! ### Support and completeness -/

/-- The *support* of an arithmetic cone system is the union of its cones. -/
def support : Set V := ⋃ σ ∈ Φ.cones, (σ : Set V)

/-- A point lies in the support exactly when some cone of the system contains it. -/
@[simp]
theorem mem_support {x : V} : x ∈ Φ.support ↔ ∃ σ ∈ Φ.cones, x ∈ σ := by
  simp [support]

/-- Every cone of an arithmetic cone system lies in its support. -/
theorem subset_support (hσ : σ ∈ Φ.cones) : (σ : Set V) ⊆ Φ.support :=
  fun _ hx ↦ Φ.mem_support.2 ⟨σ, hσ, hx⟩

/-- The support of an arithmetic cone system lies in the rational closure of the positivity
cone. -/
theorem support_subset : Φ.support ⊆ Cstar := by
  intro x hx
  obtain ⟨σ, hσ, hxσ⟩ := Φ.mem_support.1 hx
  exact Φ.coe_subset hσ hxσ

/-- The support of an arithmetic cone system is invariant under the group `Γ`. -/
@[simp]
theorem image_support {g : V ≃ₗ[ℝ] V} (hg : g ∈ Γ) : g '' Φ.support = Φ.support := by
  ext x
  simp only [Set.mem_image, mem_support]
  constructor
  · rintro ⟨y, ⟨σ, hσ, hyσ⟩, rfl⟩
    exact ⟨σ.map (g : V →ₗ[ℝ] V), Φ.map_mem hg hσ, PointedCone.mem_map.2 ⟨y, hyσ, rfl⟩⟩
  · rintro ⟨σ, hσ, hxσ⟩
    refine ⟨g⁻¹ x, ⟨σ.map ((g⁻¹ : V ≃ₗ[ℝ] V) : V →ₗ[ℝ] V), Φ.map_mem (inv_mem hg) hσ,
      PointedCone.mem_map.2 ⟨x, hxσ, rfl⟩⟩, by simp⟩

/-- An arithmetic cone system is *complete* when its support is the whole rational closure
`Cstar` of the positivity cone. This is not completeness in the ambient space. -/
def IsComplete : Prop := Φ.support = Cstar

/-- Completeness is equality of the support with `Cstar`. -/
theorem isComplete_def : Φ.IsComplete ↔ Φ.support = Cstar :=
  Iff.rfl

/-- Completeness, spelled pointwise: every point of `Cstar` lies in a cone of the system. -/
@[simp]
theorem isComplete_iff : Φ.IsComplete ↔ ∀ x ∈ Cstar, ∃ σ ∈ Φ.cones, x ∈ σ := by
  refine ⟨fun h x hx ↦ Φ.mem_support.1 (by rwa [Φ.isComplete_def.1 h]), fun h ↦ ?_⟩
  exact Φ.support_subset.antisymm fun x hx ↦ Φ.mem_support.2 (h x hx)

/-! ### The zero cone -/

/-- The arithmetic cone system consisting of the zero cone alone. It exists whenever the
rational closure of the positivity cone contains the origin. -/
def bot (hi : IsIntegralLattice i) (h0 : (0 : V) ∈ Cstar) : ArithmeticFan i Γ C Cstar where
  lattice := hi
  cones := {⊥}
  isToricCone σ hσ := by
    rw [Set.mem_singleton_iff.1 hσ]
    exact isToricCone_bot i
  coe_subset σ hσ := by
    rw [Set.mem_singleton_iff.1 hσ]
    simpa using h0
  mem_of_isFaceOf σ τ hσ hτ := by
    rw [Set.mem_singleton_iff.1 hσ] at hτ
    exact Set.mem_singleton_iff.2 (le_bot_iff.1 hτ.le)
  inf_isFaceOf_left σ τ hσ _ := by
    rw [Set.mem_singleton_iff.1 hσ, bot_inf_eq]
  map_mem g _ σ hσ := by
    rw [Set.mem_singleton_iff.1 hσ]
    exact Set.mem_singleton_iff.2 (Submodule.map_bot _)
  exists_finite_orbit_representatives :=
    ⟨{⊥}, Set.finite_singleton _, fun σ hσ ↦ ⟨⊥, rfl, 1, one_mem Γ,
      (Submodule.map_bot _).trans (Set.mem_singleton_iff.1 hσ).symm⟩⟩
  finite_setOf_inter_nonempty _ _ _ := (Set.finite_singleton _).subset fun _ hσ ↦ hσ.1

/-- The cones of the zero-cone system. -/
@[simp]
theorem bot_cones (hi : IsIntegralLattice i) (h0 : (0 : V) ∈ Cstar) :
    (bot hi h0 : ArithmeticFan i Γ C Cstar).cones = {⊥} :=
  (rfl)

/-- The support of the zero-cone system is the origin. -/
@[simp]
theorem support_bot (hi : IsIntegralLattice i) (h0 : (0 : V) ∈ Cstar) :
    (bot hi h0 : ArithmeticFan i Γ C Cstar).support = {0} := by
  ext x
  simp [Submodule.mem_bot]

/-- The zero-cone system is complete exactly when the rational closure of the positivity cone is
the origin alone. At a cusp with a positive-dimensional cone it is an arithmetic cone system that
is not complete. -/
theorem isComplete_bot_iff (hi : IsIntegralLattice i) (h0 : (0 : V) ∈ Cstar) :
    (bot hi h0 : ArithmeticFan i Γ C Cstar).IsComplete ↔ Cstar = {0} := by
  rw [isComplete_def, support_bot, eq_comm]

/-- When the rational closure of the positivity cone is the origin, as for a lattice of rank
zero, every complete arithmetic cone system consists of the zero cone alone. -/
theorem IsComplete.cones_eq_singleton_bot {Φ : ArithmeticFan i Γ C Cstar} (hΦ : Φ.IsComplete)
    (h : Cstar = {0}) : Φ.cones = {⊥} := by
  obtain ⟨σ, hσ, -⟩ := Φ.isComplete_iff.1 hΦ 0 (h ▸ Set.mem_singleton 0)
  refine Set.eq_singleton_iff_unique_mem.2 ⟨Φ.bot_mem hσ, fun τ hτ ↦ ?_⟩
  refine eq_bot_iff.2 fun x hx ↦ ?_
  have := h ▸ Φ.coe_subset hτ hx
  exact (Submodule.mem_bot _).2 (Set.mem_singleton_iff.1 this)

/-! ### Finite systems are fans -/

/-- An arithmetic cone system with finitely many cones is a finite fan with the same cones. -/
def toFiniteFan (h : Φ.cones.Finite) : Fan i where
  lattice := Φ.lattice
  cones := Φ.cones
  finite_cones := h
  isToricCone := Φ.isToricCone
  mem_of_isFaceOf := Φ.mem_of_isFaceOf
  inf_isFaceOf_left := Φ.inf_isFaceOf_left

/-- The cones of the finite fan of a finite arithmetic cone system are its cones. -/
@[simp]
theorem toFiniteFan_cones (h : Φ.cones.Finite) : (Φ.toFiniteFan h).cones = Φ.cones :=
  (rfl)

/-- The finite fan of a finite arithmetic cone system has the same support. -/
@[simp]
theorem support_toFiniteFan (h : Φ.cones.Finite) : (Φ.toFiniteFan h).support = Φ.support := by
  ext
  simp

end ArithmeticFan

namespace Fan

variable {Γ : Subgroup (V ≃ₗ[ℝ] V)} {C Cstar : Set V} (Φ : Fan i)

/-- A finite fan whose cones are permuted by `Γ` and whose support lies in `Cstar` is an
arithmetic cone system with the same cones. -/
def toArithmeticFan
    (hΓ : ∀ ⦃g⦄, g ∈ Γ → ∀ ⦃σ⦄, σ ∈ Φ.cones → σ.map (g : V →ₗ[ℝ] V) ∈ Φ.cones)
    (hC : Φ.support ⊆ Cstar) : ArithmeticFan i Γ C Cstar where
  lattice := Φ.lattice
  cones := Φ.cones
  isToricCone := Φ.isToricCone
  coe_subset _ hσ := (Φ.subset_support hσ).trans hC
  mem_of_isFaceOf := Φ.mem_of_isFaceOf
  inf_isFaceOf_left := Φ.inf_isFaceOf_left
  map_mem := hΓ
  exists_finite_orbit_representatives :=
    ⟨Φ.cones, Φ.finite_cones, fun σ hσ ↦ ⟨σ, hσ, 1, one_mem Γ, by simp⟩⟩
  finite_setOf_inter_nonempty _ _ _ := Φ.finite_cones.subset fun _ hσ ↦ hσ.1

variable (hΓ : ∀ ⦃g⦄, g ∈ Γ → ∀ ⦃σ⦄, σ ∈ Φ.cones → σ.map (g : V →ₗ[ℝ] V) ∈ Φ.cones)
  (hC : Φ.support ⊆ Cstar)

/-- The cones of the arithmetic cone system of a finite fan are the cones of the fan. -/
@[simp]
theorem toArithmeticFan_cones :
    (Φ.toArithmeticFan hΓ hC : ArithmeticFan i Γ C Cstar).cones = Φ.cones :=
  (rfl)

/-- The arithmetic cone system of a finite fan has the same support as the fan. -/
@[simp]
theorem support_toArithmeticFan :
    (Φ.toArithmeticFan hΓ hC : ArithmeticFan i Γ C Cstar).support = Φ.support := by
  ext
  simp

omit [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V] in
/-- Every group element fixing each cone of a fan permutes its cones. In particular the trivial
group, and any group acting trivially on the cones, satisfies the hypothesis of
`TauCeti.Toric.Fan.toArithmeticFan`. -/
theorem map_mem_of_forall_map_eq (h : ∀ ⦃g⦄, g ∈ Γ → ∀ ⦃σ⦄, σ ∈ Φ.cones →
    σ.map (g : V →ₗ[ℝ] V) = σ) ⦃g : V ≃ₗ[ℝ] V⦄ (hg : g ∈ Γ) ⦃σ : PointedCone ℝ V⦄
    (hσ : σ ∈ Φ.cones) : σ.map (g : V →ₗ[ℝ] V) ∈ Φ.cones :=
  (h hg hσ).symm ▸ hσ

omit [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V] in
/-- Every element of the trivial group maps each cone of a fan to a cone of the fan, so every
finite fan satisfies the hypothesis of `TauCeti.Toric.Fan.toArithmeticFan` for `Γ = ⊥`. -/
theorem map_mem_of_mem_bot ⦃g : V ≃ₗ[ℝ] V⦄ (hg : g ∈ (⊥ : Subgroup (V ≃ₗ[ℝ] V)))
    ⦃σ : PointedCone ℝ V⦄ (hσ : σ ∈ Φ.cones) : σ.map (g : V →ₗ[ℝ] V) ∈ Φ.cones :=
  Φ.map_mem_of_forall_map_eq (fun g hg σ _ ↦ by simp [Subgroup.mem_bot.1 hg]) hg hσ

/-- Viewing a finite fan as an arithmetic cone system and taking its finite fan recovers the
original fan. -/
@[simp]
theorem toArithmeticFan_toFiniteFan (h) :
    (Φ.toArithmeticFan hΓ hC : ArithmeticFan i Γ C Cstar).toFiniteFan h = Φ :=
  Fan.ext (by simp)

end Fan

namespace ArithmeticFan

variable {Γ : Subgroup (V ≃ₗ[ℝ] V)} {C Cstar : Set V} (Φ : ArithmeticFan i Γ C Cstar)

/-- Taking the finite fan of a finite arithmetic cone system and viewing it again as an
arithmetic cone system recovers the original system. -/
@[simp]
theorem toFiniteFan_toArithmeticFan (h : Φ.cones.Finite) (hΓ hC) :
    (Φ.toFiniteFan h).toArithmeticFan hΓ hC = Φ :=
  ArithmeticFan.ext (by simp)

/-! ### Change of level -/

/-- Each `Γ`-orbit of cones splits into finitely many orbits of a subgroup `Γ'` of finite index:
translate each `Γ`-orbit representative by a fixed set of representatives of `Γ ⧸ Γ'`. -/
private theorem exists_finite_orbit_representatives_of_isFiniteRelIndex
    (Γ' : Subgroup (V ≃ₗ[ℝ] V)) [Γ'.IsFiniteRelIndex Γ] :
    ∃ S : Set (PointedCone ℝ V), S.Finite ∧
      ∀ σ ∈ Φ.cones, ∃ τ ∈ S, ∃ g ∈ Γ', τ.map (g : V →ₗ[ℝ] V) = σ := by
  obtain ⟨S, hS, hrep⟩ := Φ.exists_finite_orbit_representatives
  let H : Subgroup Γ := Γ'.subgroupOf Γ
  have : H.FiniteIndex := ⟨Subgroup.IsFiniteRelIndex.relIndex_ne_zero⟩
  refine ⟨⋃ τ ∈ S, Set.range fun q : Γ ⧸ H ↦
    τ.map (((q.out⁻¹ : Γ) : V ≃ₗ[ℝ] V) : V →ₗ[ℝ] V),
    hS.biUnion fun _ _ ↦ Set.finite_range _, fun σ hσ ↦ ?_⟩
  obtain ⟨τ, hτ, g, hg, rfl⟩ := hrep σ hσ
  lift g to Γ using hg
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g⁻¹
  -- `g = h * q.out⁻¹`, where `q` is the class of `g⁻¹` and `h ∈ Γ'`.
  have hgh : g = h * (QuotientGroup.mk g⁻¹ : Γ ⧸ H).out⁻¹ := by
    rw [hh]
    group
  refine ⟨τ.map ((((QuotientGroup.mk g⁻¹ : Γ ⧸ H).out⁻¹ : Γ) : V ≃ₗ[ℝ] V) : V →ₗ[ℝ] V),
    Set.mem_biUnion hτ ⟨_, rfl⟩, (h : Γ), Subgroup.mem_subgroupOf.1 h.property, ?_⟩
  rw [← PointedCone.map_linearEquiv_mul, ← Subgroup.coe_mul, ← hgh]

/-- An arithmetic cone system for `Γ` is one for every subgroup `Γ'` of finite index in `Γ`, with
the same cones: each `Γ`-orbit splits into finitely many `Γ'`-orbits. -/
def restrict (Γ' : Subgroup (V ≃ₗ[ℝ] V)) (hle : Γ' ≤ Γ) [Γ'.IsFiniteRelIndex Γ] :
    ArithmeticFan i Γ' C Cstar where
  lattice := Φ.lattice
  cones := Φ.cones
  isToricCone := Φ.isToricCone
  coe_subset := Φ.coe_subset
  mem_of_isFaceOf := Φ.mem_of_isFaceOf
  inf_isFaceOf_left := Φ.inf_isFaceOf_left
  map_mem _ hg := Φ.map_mem (hle hg)
  exists_finite_orbit_representatives :=
    Φ.exists_finite_orbit_representatives_of_isFiniteRelIndex Γ'
  finite_setOf_inter_nonempty := Φ.finite_setOf_inter_nonempty

variable (Γ' : Subgroup (V ≃ₗ[ℝ] V)) (hle : Γ' ≤ Γ) [Γ'.IsFiniteRelIndex Γ]

/-- Restricting to a subgroup of finite index keeps the cones. -/
@[simp]
theorem restrict_cones : (Φ.restrict Γ' hle).cones = Φ.cones :=
  (rfl)

/-- Restricting to a subgroup of finite index keeps the support. -/
@[simp]
theorem support_restrict : (Φ.restrict Γ' hle).support = Φ.support :=
  (rfl)

/-- Restricting to a subgroup of finite index preserves and reflects completeness. -/
theorem isComplete_restrict_iff : (Φ.restrict Γ' hle).IsComplete ↔ Φ.IsComplete :=
  Iff.rfl

end ArithmeticFan

end TauCeti.Toric
