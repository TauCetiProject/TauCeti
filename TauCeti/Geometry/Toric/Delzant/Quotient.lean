/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
public import TauCeti.Geometry.Toric.Delzant.Level
public import TauCeti.Topology.Algebra.ProperAction.Basic

/-!
# The Delzant quotient

Let `i : N →+ V` be an integral lattice and let `(u, c)` be a facet presentation of a polytope
`Δ = {y ∈ V* | c j ≤ ⟨y, u j⟩ for every j}`. The torus `T = (ℝ / 2πℤ)^ι` acts on `ℂ^ι` by
`z_j ↦ exp(-i θ_j) z_j` (`TauCeti.torusRotation`), with moment map
`⟨μ(z), t⟩ = Σ_j t_j (½ |z_j|² + c_j)` (`TauCeti.Toric.delzantMomentMap`). The kernel torus
`N_Δ = ker (T → V / 2π i(N))` of `TauCeti.Toric.facetTorusHom` preserves the zero level `Z` of its
moment map (`TauCeti.Toric.delzantLevel`), and Delzant's construction realizes `Δ` as the moment
polytope of the quotient

`M_Δ = Z / N_Δ` (`TauCeti.Toric.DelzantQuotient i u c`).

This file constructs `M_Δ` as a topological space, the orbit space of the action of `N_Δ` on `Z`,
together with the action of the residual torus and its moment map, and proves the topological
and orbit-theoretic properties of the reduced space:

* **Topology.** The projection `Z → M_Δ` is an open quotient map. For a bounded polytope, such as
  a Delzant polytope, `M_Δ` is compact (`TauCeti.Toric.compactSpace_delzantQuotient`), since `Z`
  is. For an integral lattice `i`, the kernel torus is a closed, hence compact, subgroup of `T`, so
  it acts properly on `Z` and `M_Δ` is Hausdorff
  (`TauCeti.Toric.IsIntegralLattice.t2Space_delzantQuotient`).
* **The residual torus.** The kernel torus is normal in the commutative group `T`, so the
  residual torus `T / N_Δ` acts continuously on `M_Δ` by the action of a quotient group on the
  orbits of its kernel (`AddAction.orbitRel.Quotient.instAddActionQuotientAddGroup`). For a Delzant
  polytope and an integral lattice, `facetTorusHom` is surjective with kernel `N_Δ`, so `T / N_Δ` is
  the torus `V / 2π i(N)`.
* **Stabilizers.** The class of `θ ∈ T` fixes the class of a point `z ∈ Z` exactly when `θ` agrees
  with an element of `N_Δ` on the coordinates `j` with `z_j ≠ 0`
  (`TauCeti.Toric.DelzantQuotient.coe_vadd_mk_eq_mk_iff`). In terms of the moment value `y ∈ Δ`,
  the coordinates with `z_j = 0` are the facets active at `y`
  (`TauCeti.Toric.DelzantQuotient.coe_vadd_eq_self_iff`): the isotropy of a point over a face of
  `Δ` is the image of the coordinate subtorus of the facets containing that face. In particular
  `T / N_Δ` acts freely over the interior of `Δ`
  (`TauCeti.Toric.DelzantQuotient.vadd_eq_self_iff_of_activeSet_eq_empty`), and for a Delzant
  polytope, which has interior points, it acts effectively
  (`TauCeti.Toric.IsDelzant.faithfulVAdd_delzantQuotient`).
* **The reduced moment map.** When the real normals `i (u j)` span `V`, as they do for a Delzant
  polytope, a point `z ∈ Z` determines a unique `y ∈ V*` with `½ |z_j|² + c_j = ⟨y, u_j⟩` for every
  `j`, that is `μ(z) = β_ℝ^* y` for `β_ℝ t = Σ_j t_j i(u_j)`. This `y` is invariant under `N_Δ`, and
  defines the moment map `μ_Δ : M_Δ → V*` of the residual torus
  (`TauCeti.Toric.DelzantQuotient.reducedMomentMap`). It is continuous and invariant under the
  residual torus, its image is the polytope `Δ`
  (`TauCeti.Toric.DelzantQuotient.range_reducedMomentMap`), and its fibres are exactly the orbits
  of the residual torus (`TauCeti.Toric.DelzantQuotient.reducedMomentMap_eq_reducedMomentMap_iff`).

The smooth structure on `M_Δ` and its reduced symplectic form are not constructed here.

## Main definitions

* `TauCeti.Toric.DelzantQuotient i u c`: the orbit space `Z / N_Δ`, with the action of the residual
  torus `(ℝ / 2πℤ)^ι / N_Δ`.
* `TauCeti.Toric.DelzantQuotient.reducedMomentMap`: the moment map `M_Δ → V*` of the residual
  torus.

## Main results

* `TauCeti.Toric.compactSpace_delzantQuotient`,
  `TauCeti.Toric.IsIntegralLattice.t2Space_delzantQuotient`: `M_Δ` is compact and Hausdorff.
* `TauCeti.Toric.DelzantQuotient.coe_vadd_eq_self_iff`: the stabilizer of a point over `y ∈ Δ` is
  the image of the coordinate subtorus of the facets active at `y`.
* `TauCeti.Toric.DelzantQuotient.vadd_eq_self_iff_of_activeSet_eq_empty`: the residual torus acts
  freely over the interior of `Δ`.
* `TauCeti.Toric.IsDelzant.faithfulVAdd_delzantQuotient`: the residual torus acts effectively.
* `TauCeti.Toric.DelzantQuotient.delzantMomentMap_eq_comp_reducedMomentMap`: `μ = β_ℝ^* μ_Δ`.
* `TauCeti.Toric.DelzantQuotient.range_reducedMomentMap`: the image of `μ_Δ` is `Δ`.
* `TauCeti.Toric.DelzantQuotient.reducedMomentMap_eq_reducedMomentMap_iff`: the fibres of `μ_Δ`
  are the orbits of the residual torus.

## References

* T. Delzant, *Hamiltoniens périodiques et images convexes de l'application moment*,
  Bull. Soc. Math. France 116 (1988), 315–339.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 29.
* V. Guillemin, *Moment Maps and Combinatorial Invariants of Hamiltonian `T^n`-spaces*,
  Birkhäuser, 1994, Chapter 1.
-/

public section

noncomputable section

open Set Real

namespace TauCeti.Toric

variable {ι N V : Type*} [Fintype ι] [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {u : ι → N} {c : ι → ℝ}

/-! ### The quotient by the kernel torus -/

variable (i u c) in
/-- The Delzant quotient `M_Δ = Z / N_Δ`: the orbit space of the action of the kernel torus
`N_Δ = ker (facetTorusHom i u (2π))` on the zero level `Z` of its moment map. -/
def DelzantQuotient : Type _ :=
  AddAction.orbitRel.Quotient (facetTorusHom i u (2 * π)).ker (delzantLevel i u c)

namespace DelzantQuotient

/-- The quotient topology on the Delzant quotient. -/
instance instTopologicalSpace : TopologicalSpace (DelzantQuotient i u c) :=
  inferInstanceAs (TopologicalSpace
    (AddAction.orbitRel.Quotient (facetTorusHom i u (2 * π)).ker (delzantLevel i u c)))

/-- The projection from the level `Z` onto the Delzant quotient. -/
def mk : delzantLevel i u c → DelzantQuotient i u c :=
  Quotient.mk _

theorem mk_surjective : Function.Surjective (mk (i := i) (u := u) (c := c)) :=
  Quotient.mk_surjective

/-- To prove a property of every point of the Delzant quotient, it suffices to prove it on the
class of every point of the level. -/
@[elab_as_elim]
protected theorem inductionOn {motive : DelzantQuotient i u c → Prop} (q : DelzantQuotient i u c)
    (h : ∀ x, motive (mk x)) : motive q :=
  Quotient.inductionOn' q h

/-- Two points of the level have the same class exactly when they differ by an element of the
kernel torus. -/
theorem mk_eq_mk_iff {x y : delzantLevel i u c} :
    mk x = mk y ↔ ∃ θ ∈ (facetTorusHom i u (2 * π)).ker, θ +ᵥ y = x := by
  unfold mk DelzantQuotient
  rw [Quotient.eq, AddAction.orbitRel_apply, AddAction.mem_orbit_iff]
  exact ⟨fun ⟨θ, h⟩ ↦ ⟨θ, θ.2, h⟩, fun ⟨θ, hθ, h⟩ ↦ ⟨⟨θ, hθ⟩, h⟩⟩

/-- Elements of the kernel torus do not change the class of a point. -/
@[simp]
theorem mk_vadd_of_mem_ker {θ : ι → AddCircle (2 * π)} (hθ : θ ∈ (facetTorusHom i u (2 * π)).ker)
    (x : delzantLevel i u c) : mk (θ +ᵥ x) = mk x :=
  mk_eq_mk_iff.2 ⟨θ, hθ, rfl⟩

/-- The projection from the level onto the Delzant quotient is an open quotient map. -/
theorem isOpenQuotientMap_mk : IsOpenQuotientMap (mk (i := i) (u := u) (c := c)) :=
  AddAction.isOpenQuotientMap_quotientMk

@[fun_prop]
theorem continuous_mk : Continuous (mk (i := i) (u := u) (c := c)) :=
  isOpenQuotientMap_mk.continuous

/-! ### The residual torus action -/

/-- The action of the residual torus `(ℝ / 2πℤ)^ι / N_Δ` on the Delzant quotient, descended from
the action of `(ℝ / 2πℤ)^ι` on the level. -/
instance : AddAction ((ι → AddCircle (2 * π)) ⧸ (facetTorusHom i u (2 * π)).ker)
    (DelzantQuotient i u c) :=
  inferInstanceAs (AddAction ((ι → AddCircle (2 * π)) ⧸ (facetTorusHom i u (2 * π)).ker)
    (AddAction.orbitRel.Quotient (facetTorusHom i u (2 * π)).ker (delzantLevel i u c)))

/-- The residual torus acts on classes through representatives. -/
@[simp]
theorem coe_vadd_mk (θ : ι → AddCircle (2 * π)) (x : delzantLevel i u c) :
    (θ : (ι → AddCircle (2 * π)) ⧸ (facetTorusHom i u (2 * π)).ker) +ᵥ mk x = mk (θ +ᵥ x) :=
  (rfl)

instance : ContinuousVAdd ((ι → AddCircle (2 * π)) ⧸ (facetTorusHom i u (2 * π)).ker)
    (DelzantQuotient i u c) := by
  refine ⟨((QuotientAddGroup.isOpenQuotientMap_mk.prodMap
    isOpenQuotientMap_mk).continuous_comp_iff).1 ?_⟩
  exact (continuous_mk.comp continuous_vadd).congr fun p ↦ (coe_vadd_mk p.1 p.2).symm

/-! ### Topology -/

/-- **The Delzant quotient is Hausdorff.** For an integral lattice, the kernel torus is a closed,
hence compact, subgroup of `(ℝ / 2πℤ)^ι`, so its action on the level is proper. -/
theorem _root_.TauCeti.Toric.IsIntegralLattice.t2Space_delzantQuotient (hi : IsIntegralLattice i) :
    T2Space (DelzantQuotient i u c) := by
  have : Fact (0 < 2 * π) := ⟨two_pi_pos⟩
  have : CompactSpace (facetTorusHom i u (2 * π)).ker :=
    isCompact_iff_compactSpace.1 (hi.isClosed_ker_facetTorusHom u (2 * π)).isCompact
  have := properVAdd_of_compactSpace (facetTorusHom i u (2 * π)).ker (delzantLevel i u c)
  exact inferInstanceAs (T2Space
    (AddAction.orbitRel.Quotient (facetTorusHom i u (2 * π)).ker (delzantLevel i u c)))

/-- **The Delzant quotient of a bounded polytope is compact**, as a quotient of the compact level.
This applies to every Delzant polytope. -/
theorem _root_.TauCeti.Toric.compactSpace_delzantQuotient [FiniteDimensional ℝ V]
    (hb : Bornology.IsBounded (facetPolyhedron i u c)) : CompactSpace (DelzantQuotient i u c) := by
  have : CompactSpace (delzantLevel i u c) :=
    isCompact_iff_compactSpace.1 (isCompact_delzantLevel hb)
  exact inferInstanceAs (CompactSpace
    (AddAction.orbitRel.Quotient (facetTorusHom i u (2 * π)).ker (delzantLevel i u c)))

/-! ### Stabilizers of the residual torus -/

/-- **Stabilizers of the residual torus.** The class of `θ ∈ (ℝ / 2πℤ)^ι` in the residual torus
fixes the class of `z ∈ Z` exactly when `θ` agrees with an element of the kernel torus on every
coordinate `j` with `z_j ≠ 0`. -/
theorem coe_vadd_mk_eq_mk_iff {θ : ι → AddCircle (2 * π)} {x : delzantLevel i u c} :
    (θ : (ι → AddCircle (2 * π)) ⧸ (facetTorusHom i u (2 * π)).ker) +ᵥ mk x = mk x ↔
      ∃ n ∈ (facetTorusHom i u (2 * π)).ker,
        ∀ j, ((x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι).1 j ≠ 0 ∨
          (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι).2 j ≠ 0) → θ j = n j := by
  rw [coe_vadd_mk, mk_eq_mk_iff]
  refine exists_congr fun n ↦ and_congr_right fun _ ↦ ?_
  -- `n • x = θ • x` exactly when `θ - n` fixes `x`.
  rw [show θ +ᵥ x = n +ᵥ ((θ - n) +ᵥ x) by rw [vadd_vadd, add_sub_cancel], vadd_left_cancel_iff,
    eq_comm, ← Subtype.coe_inj, coe_vadd_delzantLevel, torusRotation_apply_eq_self_iff]
  simp only [Pi.sub_apply, sub_eq_zero]

/-! ### The reduced moment map -/

section ReducedMomentMap

variable [FiniteDimensional ℝ V]
  (hβ : Function.Surjective (Fintype.linearCombination ℝ fun j ↦ i (u j)))
include hβ

omit [FiniteDimensional ℝ V] in
/-- When the real normals span `V`, a covector is determined by its values on the normals. -/
private theorem eq_of_forall_apply_eq {y y' : StrongDual ℝ V}
    (h : ∀ j, y (i (u j)) = y' (i (u j))) : y = y' := by
  ext v
  obtain ⟨t, rfl⟩ := hβ v
  simp [Fintype.linearCombination_apply, h]

/-- The moment map `μ_Δ : M_Δ → V*` of the residual torus. When the real normals `i (u j)` span
`V`, the class of `z ∈ Z` is sent to the unique `y ∈ V*` with `½ |z_j|² + c_j = ⟨y, u_j⟩` for every
`j` (`TauCeti.Toric.DelzantQuotient.reducedMomentMap_mk_eq_iff`), that is with `μ(z) = β_ℝ^* y`
(`TauCeti.Toric.DelzantQuotient.delzantMomentMap_eq_comp_reducedMomentMap`). -/
def reducedMomentMap : DelzantQuotient i u c → StrongDual ℝ V :=
  Quotient.lift (fun x : delzantLevel i u c ↦ (mem_delzantLevel_iff.1 x.2).choose) fun x y h ↦ by
    obtain ⟨n, rfl⟩ := AddAction.orbitRel_apply.1 h
    refine eq_of_forall_apply_eq hβ fun j ↦ ?_
    rw [← (mem_delzantLevel_iff.1 (n +ᵥ y).2).choose_spec j,
      ← (mem_delzantLevel_iff.1 y.2).choose_spec j, AddSubgroup.vadd_def, coe_vadd_delzantLevel,
      torusRotation_apply_normSq]

/-- **The defining property of the reduced moment map**: `⟨μ_Δ [z], u_j⟩ = ½ |z_j|² + c_j`. -/
@[simp]
theorem reducedMomentMap_mk_apply (x : delzantLevel i u c) (j : ι) :
    reducedMomentMap hβ (mk x) (i (u j)) =
      ((x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι).1 j ^ 2 +
        (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι).2 j ^ 2) / 2 + c j :=
  ((mem_delzantLevel_iff.1 x.2).choose_spec j).symm

/-- The reduced moment map at the class of `z` is the unique `y ∈ V*` with
`½ |z_j|² + c_j = ⟨y, u_j⟩` for every `j`. -/
theorem reducedMomentMap_mk_eq_iff {x : delzantLevel i u c} {y : StrongDual ℝ V} :
    reducedMomentMap hβ (mk x) = y ↔
      ∀ j, ((x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι).1 j ^ 2 +
        (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι).2 j ^ 2) / 2 + c j = y (i (u j)) := by
  refine ⟨fun h j ↦ by rw [← h, reducedMomentMap_mk_apply], fun h ↦ ?_⟩
  exact eq_of_forall_apply_eq hβ fun j ↦ by rw [reducedMomentMap_mk_apply, h]

/-- **The reduced moment map is the moment map of the residual torus**: the moment map of the
torus `(ℝ / 2πℤ)^ι` at `z ∈ Z` is the pullback `μ(z) = β_ℝ^* μ_Δ [z]` along the map
`β_ℝ : ℝ^ι → V`, `t ↦ Σ_j t_j i(u_j)`, of Lie algebras of `(ℝ / 2πℤ)^ι → V / 2π i(N)`. -/
theorem delzantMomentMap_eq_comp_reducedMomentMap (x : delzantLevel i u c) :
    delzantMomentMap c x = (reducedMomentMap hβ (mk x)).comp
      (LinearMap.toContinuousLinearMap (Fintype.linearCombination ℝ fun j ↦ i (u j))) := by
  ext t
  simp [Fintype.linearCombination_apply, reducedMomentMap_mk_apply]

/-- The reduced moment map takes values in the polytope `Δ`. -/
theorem reducedMomentMap_mem_facetPolyhedron (q : DelzantQuotient i u c) :
    reducedMomentMap hβ q ∈ facetPolyhedron i u c := by
  induction q using DelzantQuotient.inductionOn with
  | h x => exact mem_facetPolyhedron_of_forall_eq c fun j ↦ (reducedMomentMap_mk_apply hβ x j).symm

/-- **The image of the reduced moment map is the polytope `Δ`.** -/
theorem range_reducedMomentMap :
    range (reducedMomentMap hβ (c := c)) = facetPolyhedron i u c := by
  refine (range_subset_iff.2 (reducedMomentMap_mem_facetPolyhedron hβ)).antisymm fun y hy ↦ ?_
  rw [← setOf_exists_mem_delzantLevel] at hy
  obtain ⟨x, hx, hxy⟩ := hy
  exact ⟨mk ⟨x, hx⟩, (reducedMomentMap_mk_eq_iff hβ).2 hxy⟩

/-- The reduced moment map is invariant under the residual torus. -/
@[simp]
theorem reducedMomentMap_vadd (θ : (ι → AddCircle (2 * π)) ⧸ (facetTorusHom i u (2 * π)).ker)
    (q : DelzantQuotient i u c) : reducedMomentMap hβ (θ +ᵥ q) = reducedMomentMap hβ q := by
  induction θ using QuotientAddGroup.induction_on with | H θ =>
  induction q using DelzantQuotient.inductionOn with | h x =>
  rw [coe_vadd_mk, reducedMomentMap_mk_eq_iff]
  intro j
  rw [coe_vadd_delzantLevel, torusRotation_apply_normSq, reducedMomentMap_mk_apply]

/-- The reduced moment map is continuous. -/
theorem continuous_reducedMomentMap :
    Continuous (reducedMomentMap hβ (i := i) (u := u) (c := c)) := by
  refine isOpenQuotientMap_mk.continuous_comp_iff.1 (continuous_clm_apply.2 fun v ↦ ?_)
  -- On `v = β_ℝ t`, the reduced moment map evaluates to the component `⟨μ, t⟩`.
  obtain ⟨t, rfl⟩ := hβ v
  refine ((ContinuousLinearMap.apply ℝ ℝ t).continuous.comp
    ((continuous_delzantMomentMap c).comp continuous_subtype_val)).congr fun x ↦ by
      simp [delzantMomentMap_eq_comp_reducedMomentMap hβ x]

/-- **The fibres of the reduced moment map are the orbits of the residual torus.** -/
theorem reducedMomentMap_eq_reducedMomentMap_iff {q q' : DelzantQuotient i u c} :
    reducedMomentMap hβ q = reducedMomentMap hβ q' ↔
      ∃ θ : (ι → AddCircle (2 * π)) ⧸ (facetTorusHom i u (2 * π)).ker, θ +ᵥ q' = q := by
  refine ⟨fun h ↦ ?_, fun ⟨θ, hθ⟩ ↦ by rw [← hθ, reducedMomentMap_vadd]⟩
  induction q using DelzantQuotient.inductionOn with | h x =>
  induction q' using DelzantQuotient.inductionOn with | h x' =>
  -- The two points have the same moduli `|z_j|`, so a rotation carries one to the other.
  obtain ⟨t, ht⟩ := (exists_weightRotation_apply_eq_iff (x' : EuclideanSpace ℝ ι × _) x).2
    fun j ↦ by
      have h' := congrArg (fun y : StrongDual ℝ V ↦ y (i (u j))) h
      simp only [reducedMomentMap_mk_apply] at h'
      linarith
  refine ⟨((fun j ↦ ((-t j : ℝ) : AddCircle (2 * π)) : ι → AddCircle (2 * π)) :
    (ι → AddCircle (2 * π)) ⧸ (facetTorusHom i u (2 * π)).ker), ?_⟩
  rw [coe_vadd_mk]
  congr 1
  ext1
  rw [coe_vadd_delzantLevel, torusRotation_coe]
  simpa [Pi.neg_def] using ht

/-- **Stabilizers over the faces of `Δ`.** The class of `θ ∈ (ℝ / 2πℤ)^ι` in the residual torus
fixes a point `q` of the Delzant quotient exactly when `θ` agrees with an element of the kernel
torus on every facet that is not active at `μ_Δ(q)`. So the stabilizer of a point over a face of
`Δ` is the image of the coordinate subtorus of the facets containing that face. -/
theorem coe_vadd_eq_self_iff {θ : ι → AddCircle (2 * π)} {q : DelzantQuotient i u c} :
    (θ : (ι → AddCircle (2 * π)) ⧸ (facetTorusHom i u (2 * π)).ker) +ᵥ q = q ↔
      ∃ n ∈ (facetTorusHom i u (2 * π)).ker,
        ∀ j ∉ activeSet (facetPairing i u) c (reducedMomentMap hβ q), θ j = n j := by
  induction q using DelzantQuotient.inductionOn with | h x =>
  rw [coe_vadd_mk_eq_mk_iff,
    activeSet_eq_of_forall_eq fun j ↦ (reducedMomentMap_mk_apply hβ x j).symm]
  simp only [mem_ofPred_eq, not_and_or]

/-- **The residual torus acts freely over the interior of `Δ`.** At a point `q` whose moment value
lies on no facet, only the identity of the residual torus fixes `q`. -/
theorem vadd_eq_self_iff_of_activeSet_eq_empty {q : DelzantQuotient i u c}
    (hq : activeSet (facetPairing i u) c (reducedMomentMap hβ q) = ∅)
    {θ : (ι → AddCircle (2 * π)) ⧸ (facetTorusHom i u (2 * π)).ker} : θ +ᵥ q = q ↔ θ = 0 := by
  induction θ using QuotientAddGroup.induction_on with | H θ =>
  rw [coe_vadd_eq_self_iff hβ, hq, QuotientAddGroup.eq_zero_iff]
  refine ⟨fun ⟨n, hn, h⟩ ↦ ?_, fun h ↦ ⟨θ, h, fun _ _ ↦ rfl⟩⟩
  rwa [funext fun j ↦ h j (notMem_empty j)]

end ReducedMomentMap

end DelzantQuotient

/-- **The residual torus acts effectively.** For a Delzant polytope, an element of
`(ℝ / 2πℤ)^ι / N_Δ` that fixes every point of the Delzant quotient is trivial; indeed it already
acts freely over the interior of `Δ`. Equivalently, an element of `(ℝ / 2πℤ)^ι` acts trivially on
`M_Δ` exactly when it lies in the kernel torus `N_Δ`. -/
theorem IsDelzant.faithfulVAdd_delzantQuotient [FiniteDimensional ℝ V] (hΔ : IsDelzant i u c)
    (hi : IsIntegralLattice i) :
    FaithfulVAdd ((ι → AddCircle (2 * π)) ⧸ (facetTorusHom i u (2 * π)).ker)
      (DelzantQuotient i u c) := by
  have hβ := surjective_linearCombination_real hi.span_range_eq_top hΔ.surjective_linearCombination
  -- A point of `M_Δ` over an interior point of `Δ`.
  obtain ⟨y, hy, hy₀⟩ := hΔ.exists_activeSet_eq_empty hi.injective
  rw [← DelzantQuotient.range_reducedMomentMap hβ] at hy
  obtain ⟨q, rfl⟩ := hy
  refine ⟨fun {θ θ'} h ↦ sub_eq_zero.1 ?_⟩
  rw [← DelzantQuotient.vadd_eq_self_iff_of_activeSet_eq_empty hβ hy₀, sub_eq_neg_add, ← vadd_vadd,
    h q, neg_vadd_vadd]

end TauCeti.Toric
