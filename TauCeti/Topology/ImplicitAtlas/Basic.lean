/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Finset.Update
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.Maps.OpenQuotient
public import Mathlib.Topology.OpenPartialHomeomorph.Defs
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Implicit atlases

An *implicit atlas* of virtual dimension `d` on a space `X`, indexed by a set `A`, is Pardon's
topological replacement for a Kuranishi structure on a moduli space of pseudoholomorphic curves.
It is the input from which virtual fundamental cycles are built. Its data are:

* for every `α ∈ A`, a finite group `Γ_α` and a finite-dimensional real representation `E_α`
  (the *obstruction space*), given here as parameters `Γ`, `E` and `ρ`;
* for every finite `I ⊆ A`, a Hausdorff space `X_I` (the *thickening*) with a continuous action
  of `Γ_I = ∏_(α ∈ I) Γ_α`, given here as parameters `T` and `act`, and an identification
  `X_∅ ≃ₜ X` (`ImplicitAtlas.Core.baseHomeomorph`);
* for every `α ∈ I`, a continuous equivariant *Kuranishi map* `s_α : X_I → E_α`
  (`ImplicitAtlas.Core.kuranishi`), on which the factors `Γ_β` with `β ≠ α` act trivially;
* for every finite `I`, an invariant open *regular locus* `X_I^reg ⊆ X_I`
  (`ImplicitAtlas.Core.regLocus`), on which the thickening is a topological manifold;
* for finite `I ⊆ J`, an equivariant continuous *footprint map*
  `ψ_IJ : Z_IJ → X_I` (`ImplicitAtlas.Core.footprintMap`) defined on the zero set
  `Z_IJ = {x ∈ X_J | s_α(x) = 0 for all α ∈ J \ I}` (`TauCeti.kuranishiZeroSet`).

The axioms say that the footprint maps form a cocycle compatible with the Kuranishi maps, that
`ψ_IJ` identifies `Z_IJ / Γ_(J \ I)` with its open image `U_IJ ⊆ X_I`, that the images satisfy
`U_IJ₁ ∩ U_IJ₂ = U_I(J₁ ∪ J₂)` and `ψ_IJ⁻¹(U_IK) = U_JK ∩ Z_IJ`, that `Γ_(J \ I)` acts freely
over the regular locus, that over the regular locus the extra obstruction `s_(J \ I)`
(`TauCeti.kuranishiSdiff`) is locally a product projection `ℝ^(d + m_I) × E_(J \ I) → E_(J \ I)`
with `m_I = ∑_(α ∈ I) dim E_α`, and that the regular *footprints* `V_I = ψ_∅I(X_I^reg ∩ Z_∅I)`
cover `X`. The images `U_IJ` are not separate data:
the quotient axiom makes `ψ_IJ` surjective onto `U_IJ`, so here `U_IJ` is the range of `ψ_IJ`.
The regular locus is part of the data; outside it the thickening need not be a manifold and the
action need not be free.

This file states the definition (`TauCeti.ImplicitAtlas`) and proves its first consequences. All
data and axioms other than the local product model form `TauCeti.ImplicitAtlas.Core`, which
implicit atlases with boundary also extend, and the consequences not involving the product model
are proved for it. The zero sets are invariant
(`TauCeti.ImplicitAtlas.Core.act_mem_kuranishiZeroSet`), the images `U_IJ` are invariant under
`Γ_I` (`TauCeti.ImplicitAtlas.Core.act_mem_range_footprintMap`), the zero-set domains of the
cocycle condition match (`TauCeti.ImplicitAtlas.Core.mem_kuranishiZeroSet_iff_footprintMap_mem`),
the footprint maps are open quotient maps onto their images
(`TauCeti.ImplicitAtlas.Core.isOpenQuotientMap_footprintMap`),
near a point of `Z_SJ` over `X_S^reg` every point of `Z_(S'J)`, `S ⊆ S' ⊆ J`, lies over
`X_(S')^reg` (`TauCeti.ImplicitAtlas.Core.exists_isOpen_forall_footprintMap_mem_regLocus`),
the footprints are open and cover `X` (`TauCeti.ImplicitAtlas.Core.isOpen_footprint`,
`TauCeti.ImplicitAtlas.Core.iUnion_footprint`) and are empty where the regular locus is
(`TauCeti.ImplicitAtlas.Core.footprint_eq_empty_of_regLocus_eq_empty`), they satisfy the
*footprint conditions* `V_I ∩ V_K ⊆ V_J` for `I ⊆ J ⊆ K` and `V_I ∩ V_J ⊆ V_(I ∪ J)`
(`TauCeti.ImplicitAtlas.Core.footprint_inter_footprint_subset_footprint`,
`TauCeti.ImplicitAtlas.Core.footprint_inter_footprint_subset_footprint_union`), which make the
cover `{V_I}` suitable for gluing local data indexed by pairs `I ⊆ J`. Every point of the
regular locus `X_I^reg` has a chart to `ℝ^(d + m_I)`
(`TauCeti.ImplicitAtlas.exists_openPartialHomeomorph_of_mem_regLocus`), so the regular locus is
empty where the expected dimension `d + m_I` is negative
(`TauCeti.ImplicitAtlas.regLocus_eq_empty_of_neg`), so that a nonempty space carries no atlas
whose expected dimensions are all negative (`TauCeti.ImplicitAtlas.isEmpty_of_forall_neg`).
A point of `Z_IJ` fixed by a nontrivial element of `Γ_(J \ I)` does not lie over `X_I^reg`
(`TauCeti.ImplicitAtlas.Core.footprintMap_notMem_regLocus_of_act_eq`), so an ineffective point
has no regular base (`TauCeti.ImplicitAtlas.Core.regLocus_empty_eq_empty_of_nontrivial`).
Examples are in `TauCeti.Topology.ImplicitAtlas.Examples`.

## Implementation notes

* The groups, obstruction spaces, thickenings and actions are parameters, and the action of `Γ_I`
  on `X_I` is a homomorphism `act I` into the group of homeomorphisms of `X_I`, that is, a
  continuous action of the discrete group `Γ_I`.
* The quotient axiom is stated as two conditions: `ψ_IJ` corestricted to its range is a quotient
  map, and its fibres are the orbits of the subgroup `Γ_(J \ I) = {g ∈ Γ_J | g|_I = 1}`. Together
  they say that `ψ_IJ` induces a homeomorphism `Z_IJ / Γ_(J \ I) ≃ₜ U_IJ`.
* The product axiom over the regular locus is a local homeomorphism `e` of `X_J` into
  `ℝ^n × E_(J \ I)` with `(n : ℤ) = d + m_I` whose second component is `s_(J \ I)`. Its target is
  open, so it contains a product of open sets around each of its points, as in the formulation
  with product neighbourhoods. For `I = J` it says that `X_I^reg` is a topological manifold of
  dimension `d + m_I`, which forces `d + m_I ≥ 0` wherever the regular locus is nonempty.
* The finiteness of the groups `Γ α`, the finite-dimensionality of the spaces `E α` and the
  Hausdorff property of the thickenings are part of the definition, as in Pardon's. The first
  consequences proved here do not use them; the rational virtual complexes built from an atlas
  (invariants of finite groups, orientation lines of the `E α`) do.
* Compactness and the Hausdorff property of `X` are not part of the structure: they are hypotheses
  of the theorems that need them, such as the existence of finite subatlases.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), 779–1034, Definition 3.1.1 (implicit
  atlases) and Example 2.3.2 (the atlas `s(x) = xⁿ` on a point).
-/

public section

open Set Topology

namespace TauCeti

variable {A : Type*}

/-- The zero set `Z_IJ = {x ∈ X_J | s_α(x) = 0 for all α ∈ J \ I}` of a family of Kuranishi maps
`s J α : X_J → E_α`, `α ∈ J`. It is the domain of the footprint map `ψ_IJ` of an implicit atlas.
For `I = ∅` it is the zero set of all of `s_J`, and for `J ⊆ I` it is all of `X_J`. -/
def kuranishiZeroSet {T : Finset A → Type*} {E : A → Type*} [∀ α, Zero (E α)]
    (s : ∀ (J : Finset A) (α : J), T J → E α) (I J : Finset A) : Set (T J) :=
  {x | ∀ α : J, α.val ∉ I → s J α x = 0}

@[simp]
theorem mem_kuranishiZeroSet {T : Finset A → Type*} {E : A → Type*} [∀ α, Zero (E α)]
    {s : ∀ (J : Finset A) (α : J), T J → E α} {I J : Finset A} {x : T J} :
    x ∈ kuranishiZeroSet s I J ↔ ∀ α : J, α.val ∉ I → s J α x = 0 :=
  Iff.rfl

theorem kuranishiZeroSet_eq_univ {T : Finset A → Type*} {E : A → Type*} [∀ α, Zero (E α)]
    (s : ∀ (J : Finset A) (α : J), T J → E α) {I J : Finset A} (h : J ⊆ I) :
    kuranishiZeroSet s I J = univ :=
  eq_univ_of_forall fun _ ↦ mem_kuranishiZeroSet.2 fun α hα ↦ (hα (h α.property)).elim

/-- Every point of `X_I` lies in `Z_II`, the domain of the footprint map `ψ_II`. -/
theorem mem_kuranishiZeroSet_self {T : Finset A → Type*} {E : A → Type*} [∀ α, Zero (E α)]
    (s : ∀ (J : Finset A) (α : J), T J → E α) {I : Finset A} (x : T I) :
    x ∈ kuranishiZeroSet s I I :=
  mem_kuranishiZeroSet.2 fun α hα ↦ (hα α.property).elim

/-- The zero set `Z_IJ` grows with `I`: fewer Kuranishi maps are required to vanish. -/
theorem kuranishiZeroSet_mono {T : Finset A → Type*} {E : A → Type*} [∀ α, Zero (E α)]
    (s : ∀ (J : Finset A) (α : J), T J → E α) {I I' : Finset A} (h : I ⊆ I') (J : Finset A) :
    kuranishiZeroSet s I J ⊆ kuranishiZeroSet s I' J :=
  fun _ hx ↦ mem_kuranishiZeroSet.2 fun α hα ↦ mem_kuranishiZeroSet.1 hx α fun hαI ↦ hα (h hαI)

/-- The extra obstruction `s_(J \ I) : X_J → E_(J \ I) = ∏_(α ∈ J \ I) E_α` of a family of
Kuranishi maps `s J α : X_J → E_α`: the components of `s_J` indexed by `J \ I`. Its zero set is
`Z_IJ` (`TauCeti.kuranishiSdiff_eq_zero_iff`). -/
def kuranishiSdiff [DecidableEq A] {T : Finset A → Type*} {E : A → Type*}
    (s : ∀ (J : Finset A) (α : J), T J → E α) (I J : Finset A) (y : T J) :
    (α : ↥(J \ I)) → E α :=
  fun α ↦ s J ⟨α.val, (Finset.mem_sdiff.1 α.property).1⟩ y

@[simp]
theorem kuranishiSdiff_apply [DecidableEq A] {T : Finset A → Type*} {E : A → Type*}
    (s : ∀ (J : Finset A) (α : J), T J → E α) (I J : Finset A) (y : T J) (α : ↥(J \ I)) :
    kuranishiSdiff s I J y α = s J ⟨α.val, (Finset.mem_sdiff.1 α.property).1⟩ y := by
  simp only [kuranishiSdiff]

/-- The zero set of the extra obstruction `s_(J \ I)` is `Z_IJ`. -/
theorem kuranishiSdiff_eq_zero_iff [DecidableEq A] {T : Finset A → Type*} {E : A → Type*}
    [∀ α, Zero (E α)] {s : ∀ (J : Finset A) (α : J), T J → E α} {I J : Finset A} {y : T J} :
    kuranishiSdiff s I J y = 0 ↔ y ∈ kuranishiZeroSet s I J := by
  simp only [funext_iff, kuranishiSdiff_apply, Pi.zero_apply, mem_kuranishiZeroSet]
  exact ⟨fun h α hα ↦ h ⟨α.val, Finset.mem_sdiff.2 ⟨α.property, hα⟩⟩,
    fun h α ↦ h _ (Finset.mem_sdiff.1 α.property).2⟩

/-- The data and axioms of an implicit atlas (`TauCeti.ImplicitAtlas`) other than its local
product model over the regular locus, which is the only axiom involving the virtual dimension.
Implicit atlases and implicit atlases with boundary (`TauCeti.ImplicitAtlasWithBoundary`) both
extend it, with their own product models, and share the consequences proved for it here. See the
module docstring for the meaning of each field. -/
structure ImplicitAtlas.Core [DecidableEq A] (Γ : A → Type*) [∀ α, Group (Γ α)]
    [∀ α, Finite (Γ α)] (E : A → Type*) [∀ α, NormedAddCommGroup (E α)]
    [∀ α, NormedSpace ℝ (E α)] [∀ α, FiniteDimensional ℝ (E α)]
    (ρ : ∀ α, Representation ℝ (Γ α) (E α))
    (T : Finset A → Type*) [∀ I, TopologicalSpace (T I)] [∀ I, T2Space (T I)]
    (act : ∀ I : Finset A, ((α : I) → Γ α) →* (T I ≃ₜ T I))
    (X : Type*) [TopologicalSpace X] where
  /-- The identification `X_∅ ≃ₜ X` of the thickening at the empty index set. -/
  baseHomeomorph : T ∅ ≃ₜ X
  /-- The Kuranishi map `s_α : X_I → E_α`, for `α ∈ I`. -/
  kuranishi : ∀ (I : Finset A) (α : I), T I → E α
  continuous_kuranishi : ∀ (I : Finset A) (α : I), Continuous (kuranishi I α)
  /-- The Kuranishi map `s_α` is `Γ_α`-equivariant, and the other factors of `Γ_I` act trivially
  on `E_α`. -/
  kuranishi_act : ∀ (I : Finset A) (α : I) (g : (β : I) → Γ β) (x : T I),
    kuranishi I α (act I g x) = ρ α (g α) (kuranishi I α x)
  /-- The regular locus `X_I^reg ⊆ X_I`. -/
  regLocus : ∀ I : Finset A, Set (T I)
  isOpen_regLocus : ∀ I : Finset A, IsOpen (regLocus I)
  act_mem_regLocus : ∀ (I : Finset A) (g : (α : I) → Γ α) (x : T I),
    x ∈ regLocus I → act I g x ∈ regLocus I
  /-- The footprint map `ψ_IJ : Z_IJ → X_I`, for `I ⊆ J`. -/
  footprintMap : ∀ ⦃I J : Finset A⦄, I ⊆ J → kuranishiZeroSet kuranishi I J → T I
  continuous_footprintMap : ∀ ⦃I J : Finset A⦄ (h : I ⊆ J), Continuous (footprintMap h)
  /-- The footprint map `ψ_IJ` is equivariant, with `Γ_J` acting on `X_I` through the
  restriction `Γ_J → Γ_I`. -/
  footprintMap_act : ∀ ⦃I J : Finset A⦄ (h : I ⊆ J) (g : (α : J) → Γ α)
    (x : kuranishiZeroSet kuranishi I J)
    (hx : act J g x ∈ kuranishiZeroSet kuranishi I J),
    footprintMap h ⟨act J g x, hx⟩ = act I (Finset.restrict₂ (π := Γ) h g) (footprintMap h x)
  footprintMap_self : ∀ (I : Finset A) (x : T I),
    footprintMap (subset_refl I) ⟨x, mem_kuranishiZeroSet_self kuranishi x⟩ = x
  /-- The cocycle condition `ψ_IJ ∘ ψ_JK = ψ_IK` on the common domain. -/
  footprintMap_footprintMap : ∀ ⦃I J K : Finset A⦄ (hIJ : I ⊆ J) (hJK : J ⊆ K)
    (x : kuranishiZeroSet kuranishi J K)
    (hx : footprintMap hJK x ∈ kuranishiZeroSet kuranishi I J)
    (hx' : x.val ∈ kuranishiZeroSet kuranishi I K),
    footprintMap hIJ ⟨footprintMap hJK x, hx⟩ = footprintMap (hIJ.trans hJK) ⟨x, hx'⟩
  /-- The Kuranishi maps are compatible with the footprint maps: `s_I ∘ ψ_IJ = s_I`. -/
  kuranishi_footprintMap : ∀ ⦃I J : Finset A⦄ (h : I ⊆ J) (x : kuranishiZeroSet kuranishi I J)
    (α : I),
    kuranishi I α (footprintMap h x) = kuranishi J ⟨α, h α.property⟩ x
  isOpen_range_footprintMap : ∀ ⦃I J : Finset A⦄ (h : I ⊆ J), IsOpen (range (footprintMap h))
  /-- `U_IJ₁ ∩ U_IJ₂ = U_I(J₁ ∪ J₂)`. -/
  range_footprintMap_inter : ∀ ⦃I J₁ J₂ : Finset A⦄ (h₁ : I ⊆ J₁) (h₂ : I ⊆ J₂),
    range (footprintMap h₁) ∩ range (footprintMap h₂) =
      range (footprintMap (h₁.trans (Finset.subset_union_left (s₂ := J₂))))
  /-- `ψ_IJ⁻¹(U_IK) = U_JK ∩ Z_IJ`. -/
  footprintMap_mem_range_iff : ∀ ⦃I J K : Finset A⦄ (hIJ : I ⊆ J) (hJK : J ⊆ K)
    (x : kuranishiZeroSet kuranishi I J),
    footprintMap hIJ x ∈ range (footprintMap (hIJ.trans hJK)) ↔ x.val ∈ range (footprintMap hJK)
  /-- The footprint map is a quotient map onto its image `U_IJ`. -/
  isQuotientMap_footprintMap : ∀ ⦃I J : Finset A⦄ (h : I ⊆ J),
    IsQuotientMap (rangeFactorization (footprintMap h))
  /-- The fibres of the footprint map `ψ_IJ` are the orbits of `Γ_(J \ I)`. -/
  footprintMap_eq_footprintMap_iff : ∀ ⦃I J : Finset A⦄ (h : I ⊆ J)
    (x y : kuranishiZeroSet kuranishi I J),
    footprintMap h x = footprintMap h y ↔
      ∃ g : (α : J) → Γ α, Finset.restrict₂ (π := Γ) h g = 1 ∧ act J g x = y
  /-- `ψ_IJ⁻¹(X_I^reg) ⊆ X_J^reg`. -/
  mem_regLocus_of_footprintMap_mem : ∀ ⦃I J : Finset A⦄ (h : I ⊆ J)
    (x : kuranishiZeroSet kuranishi I J),
    footprintMap h x ∈ regLocus I → x.val ∈ regLocus J
  /-- `Γ_(J \ I)` acts freely on `ψ_IJ⁻¹(X_I^reg)`. -/
  eq_one_of_act_eq : ∀ ⦃I J : Finset A⦄ (h : I ⊆ J) (x : kuranishiZeroSet kuranishi I J),
    footprintMap h x ∈ regLocus I → ∀ g : (α : J) → Γ α,
      Finset.restrict₂ (π := Γ) h g = 1 → act J g x = x → g = 1
  /-- The regular footprints `V_I = ψ_∅I(X_I^reg ∩ Z_∅I)` cover `X`. -/
  exists_footprintMap_eq : ∀ y : X, ∃ (I : Finset A) (x : kuranishiZeroSet kuranishi ∅ I),
    x.val ∈ regLocus I ∧ baseHomeomorph (footprintMap (Finset.empty_subset I) x) = y

/-- An **implicit atlas** of virtual dimension `d` on `X` (Pardon, Definition 3.1.1), with finite
isotropy groups `Γ α`, obstruction representations `ρ α` on `E α`, thickenings `T I` and actions
`act I` of `Γ_I = ∏_(α ∈ I) Γ α` on them. Its data and all axioms but the product model are those
of `TauCeti.ImplicitAtlas.Core`; see the module docstring for the meaning of each field. The
image `U_IJ` of the footprint map `ψ_IJ` is `Set.range (footprintMap h)`. -/
structure ImplicitAtlas [DecidableEq A] (Γ : A → Type*) [∀ α, Group (Γ α)] [∀ α, Finite (Γ α)]
    (E : A → Type*) [∀ α, NormedAddCommGroup (E α)] [∀ α, NormedSpace ℝ (E α)]
    [∀ α, FiniteDimensional ℝ (E α)] (ρ : ∀ α, Representation ℝ (Γ α) (E α))
    (T : Finset A → Type*) [∀ I, TopologicalSpace (T I)] [∀ I, T2Space (T I)]
    (act : ∀ I : Finset A, ((α : I) → Γ α) →* (T I ≃ₜ T I))
    (X : Type*) [TopologicalSpace X] (d : ℤ) extends ImplicitAtlas.Core Γ E ρ T act X where
  /-- Over `ψ_IJ⁻¹(X_I^reg)`, the map `s_(J \ I) : X_J → E_(J \ I)` is locally a product
  projection `ℝ^(d + m_I) × E_(J \ I) → E_(J \ I)`. -/
  exists_openPartialHomeomorph : ∀ ⦃I J : Finset A⦄ (h : I ⊆ J)
    (x : kuranishiZeroSet kuranishi I J),
    footprintMap h x ∈ regLocus I → ∃ n : ℕ,
      (n : ℤ) = d + ∑ α ∈ I, (Module.finrank ℝ (E α) : ℤ) ∧
      ∃ e : OpenPartialHomeomorph (T J) (EuclideanSpace ℝ (Fin n) × ((α : ↥(J \ I)) → E α)),
        x.val ∈ e.source ∧ ∀ y ∈ e.source, (e y).2 = kuranishiSdiff kuranishi I J y

namespace ImplicitAtlas

variable [DecidableEq A] {Γ : A → Type*} [∀ α, Group (Γ α)] [∀ α, Finite (Γ α)]
  {E : A → Type*} [∀ α, NormedAddCommGroup (E α)] [∀ α, NormedSpace ℝ (E α)]
  [∀ α, FiniteDimensional ℝ (E α)] {ρ : ∀ α, Representation ℝ (Γ α) (E α)}
  {T : Finset A → Type*} [∀ I, TopologicalSpace (T I)] [∀ I, T2Space (T I)]
  {act : ∀ I : Finset A, ((α : I) → Γ α) →* (T I ≃ₜ T I)}
  {X : Type*} [TopologicalSpace X] {d : ℤ}

namespace Core

variable (𝒜 : ImplicitAtlas.Core Γ E ρ T act X)

/-- The zero sets `Z_IJ` are invariant under `Γ_J`. -/
theorem act_mem_kuranishiZeroSet {I J : Finset A} (g : (α : J) → Γ α) {x : T J}
    (hx : x ∈ kuranishiZeroSet 𝒜.kuranishi I J) :
    act J g x ∈ kuranishiZeroSet 𝒜.kuranishi I J := mem_kuranishiZeroSet.2 fun α hα ↦ by
  rw [𝒜.kuranishi_act, mem_kuranishiZeroSet.1 hx α hα, map_zero]

/-- The domains of the cocycle condition match: for `J ⊆ K`, a point `x` of `Z_JK` lies in
`Z_IK` exactly when `ψ_JK x` lies in `Z_IJ`. -/
theorem mem_kuranishiZeroSet_iff_footprintMap_mem {I J K : Finset A} (hJK : J ⊆ K)
    (x : kuranishiZeroSet 𝒜.kuranishi J K) :
    x.val ∈ kuranishiZeroSet 𝒜.kuranishi I K ↔
      𝒜.footprintMap hJK x ∈ kuranishiZeroSet 𝒜.kuranishi I J := by
  simp only [mem_kuranishiZeroSet]
  refine ⟨fun hx α hα ↦ ?_, fun hx α hα ↦ ?_⟩
  · rw [𝒜.kuranishi_footprintMap]
    exact hx _ hα
  · by_cases hαJ : α.val ∈ J
    · simpa [𝒜.kuranishi_footprintMap] using hx ⟨α, hαJ⟩ hα
    · exact mem_kuranishiZeroSet.1 x.property α hαJ

/-- The cocycle condition `ψ_IJ ∘ ψ_JK = ψ_IK`, with the domain of `ψ_IJ` supplied by
`ImplicitAtlas.Core.mem_kuranishiZeroSet_iff_footprintMap_mem`. -/
theorem footprintMap_footprintMap_mk {I J K : Finset A} (hIJ : I ⊆ J) (hJK : J ⊆ K)
    (x : kuranishiZeroSet 𝒜.kuranishi J K) (hx : x.val ∈ kuranishiZeroSet 𝒜.kuranishi I K) :
    𝒜.footprintMap hIJ
        ⟨𝒜.footprintMap hJK x, (𝒜.mem_kuranishiZeroSet_iff_footprintMap_mem hJK x).1 hx⟩ =
      𝒜.footprintMap (hIJ.trans hJK) ⟨x, hx⟩ :=
  𝒜.footprintMap_footprintMap hIJ hJK x _ hx

/-- The footprint map `ψ_II` is the identity, so `U_II = X_I`. -/
@[simp]
theorem range_footprintMap_self (I : Finset A) :
    range (𝒜.footprintMap (subset_refl I)) = univ :=
  eq_univ_of_forall fun x ↦ ⟨_, 𝒜.footprintMap_self I x⟩

/-- The image `U_IJ` of the footprint map `ψ_IJ` is invariant under `Γ_I`. -/
theorem act_mem_range_footprintMap {I J : Finset A} (h : I ⊆ J) (g : (α : I) → Γ α) {y : T I}
    (hy : y ∈ range (𝒜.footprintMap h)) : act I g y ∈ range (𝒜.footprintMap h) := by
  obtain ⟨x, rfl⟩ := hy
  refine ⟨⟨act J (J.restrict (Function.updateFinset 1 I g)) x,
    𝒜.act_mem_kuranishiZeroSet _ x.property⟩, ?_⟩
  rw [𝒜.footprintMap_act, ← Function.comp_apply (f := Finset.restrict₂ h),
    Finset.restrict₂_comp_restrict, Function.restrict_updateFinset]

/-- Points of `Z_IJ` with the same image under `ψ_IJ` lie together in `ψ_IJ⁻¹(X_I^reg)` or
outside it, since they lie in one orbit and the regular locus is invariant. -/
theorem mem_regLocus_of_footprintMap_eq {I J : Finset A} (h : I ⊆ J)
    {x y : kuranishiZeroSet 𝒜.kuranishi I J} (hxy : 𝒜.footprintMap h x = 𝒜.footprintMap h y)
    (hx : x.val ∈ 𝒜.regLocus J) : y.val ∈ 𝒜.regLocus J := by
  obtain ⟨g, -, hg⟩ := (𝒜.footprintMap_eq_footprintMap_iff h x y).1 hxy
  exact hg ▸ 𝒜.act_mem_regLocus J g x hx

/-- The images `U_IJ` of footprint maps with equal targets `J = J'` agree. -/
theorem range_footprintMap_eq_of_eq {I J J' : Finset A} (h : I ⊆ J) (h' : I ⊆ J')
    (hJ : J = J') : range (𝒜.footprintMap h) = range (𝒜.footprintMap h') := by
  subst hJ
  rfl

/-- The footprint map `ψ_IJ`, corestricted to its image `U_IJ`, is an open quotient map. Unlike
quotient maps, open quotient maps are stable under products, so the footprint maps of a product of
implicit atlases are again quotient maps onto their images. -/
theorem isOpenQuotientMap_footprintMap {I J : Finset A} (h : I ⊆ J) :
    IsOpenQuotientMap (rangeFactorization (𝒜.footprintMap h)) := by
  -- The saturation of an open set `U ⊆ Z_IJ` is the union of its preimages under the elements of
  -- `Γ_(J \ I)`, since the fibres of `ψ_IJ` are the orbits of `Γ_(J \ I)`, so it is open, and its
  -- image is open by the quotient axiom.
  set q := rangeFactorization (𝒜.footprintMap h)
  have hq : IsQuotientMap q := 𝒜.isQuotientMap_footprintMap h
  -- The action of `g ∈ Γ_J` on the invariant zero set `Z_IJ`.
  let actZ (g : (α : J) → Γ α) (x : kuranishiZeroSet 𝒜.kuranishi I J) :
      kuranishiZeroSet 𝒜.kuranishi I J :=
    ⟨act J g x, 𝒜.act_mem_kuranishiZeroSet g x.property⟩
  refine .of_isOpenMap_isQuotientMap (fun U hU ↦ ?_) hq
  have hsat : q ⁻¹' (q '' U) =
      ⋃ g ∈ {g : (α : J) → Γ α | Finset.restrict₂ (π := Γ) h g = 1}, actZ g ⁻¹' U := by
    ext x
    simp only [mem_preimage, mem_image, mem_iUnion, mem_ofPred_eq, exists_prop]
    constructor
    · rintro ⟨u, hu, hux⟩
      obtain ⟨g, hg, hgx⟩ :=
        (𝒜.footprintMap_eq_footprintMap_iff h x u).1 (congrArg Subtype.val hux).symm
      exact ⟨g, hg, by rwa [show actZ g x = u from Subtype.ext hgx]⟩
    · rintro ⟨g, hg, hgx⟩
      exact ⟨_, hgx, Subtype.ext ((𝒜.footprintMap_eq_footprintMap_iff h _ _).2 ⟨g, hg, rfl⟩).symm⟩
  rw [← hq.isOpen_preimage, hsat]
  exact isOpen_biUnion fun g _ ↦ hU.preimage
    (((act J g).continuous.comp continuous_subtypeVal).subtype_mk _)

/-- **Regularity is open near a regular point.** Let `x ∈ Z_SJ` lie over the regular locus
`X_S^reg`. Then there is a neighbourhood `W` of `x` in `X_J` such that every point `y ∈ W` of the
zero set `Z_(S'J)`, for any `S ⊆ S' ⊆ J`, lies over `X_(S')^reg`. -/
theorem exists_isOpen_forall_footprintMap_mem_regLocus {S J : Finset A} (hSJ : S ⊆ J)
    (x : kuranishiZeroSet 𝒜.kuranishi S J) (hx : 𝒜.footprintMap hSJ x ∈ 𝒜.regLocus S) :
    ∃ W : Set (T J), IsOpen W ∧ x.val ∈ W ∧ ∀ ⦃S' : Finset A⦄ (_ : S ⊆ S') (hS'J : S' ⊆ J)
      (y : kuranishiZeroSet 𝒜.kuranishi S' J), y.val ∈ W →
        𝒜.footprintMap hS'J y ∈ 𝒜.regLocus S' := by
  -- For each of the finitely many `S'`, the point `ψ_S'J(x)` is regular, and regularity is open
  -- in `Z_S'J`.
  have key : ∀ S' ∈ J.powerset.filter (S ⊆ ·), ∃ W : Set (T J), IsOpen W ∧ x.val ∈ W ∧
      ∀ (hS'J : S' ⊆ J) (y : kuranishiZeroSet 𝒜.kuranishi S' J), y.val ∈ W →
        𝒜.footprintMap hS'J y ∈ 𝒜.regLocus S' := by
    intro S' hS'
    obtain ⟨hS'J, hSS'⟩ := Finset.mem_filter.1 hS'
    rw [Finset.mem_powerset] at hS'J
    have hx' : x.val ∈ kuranishiZeroSet 𝒜.kuranishi S' J :=
      kuranishiZeroSet_mono _ hSS' J x.property
    have hreg : 𝒜.footprintMap hS'J ⟨x, hx'⟩ ∈ 𝒜.regLocus S' := by
      refine 𝒜.mem_regLocus_of_footprintMap_mem hSS' ⟨_,
        (𝒜.mem_kuranishiZeroSet_iff_footprintMap_mem hS'J ⟨x, hx'⟩).1 x.property⟩ ?_
      rwa [𝒜.footprintMap_footprintMap_mk hSS' hS'J ⟨x, hx'⟩ x.property]
    obtain ⟨W, hW, hWeq⟩ := isOpen_induced_iff.1
      ((𝒜.isOpen_regLocus S').preimage (𝒜.continuous_footprintMap hS'J))
    refine ⟨W, hW, ?_, fun _ y hy ↦ ?_⟩
    · exact Set.mem_preimage.1 ((Set.ext_iff.1 hWeq _).2 (Set.mem_preimage.2 hreg))
    · exact Set.mem_preimage.1 ((Set.ext_iff.1 hWeq y).1 (Set.mem_preimage.2 hy))
  choose! W hW hxW hWreg using key
  refine ⟨⋂ S' ∈ J.powerset.filter (S ⊆ ·), W S', isOpen_biInter_finset hW,
    mem_iInter₂.2 hxW, fun S' hSS' hS'J y hy ↦ ?_⟩
  have hmem : S' ∈ J.powerset.filter (S ⊆ ·) := by simp [hS'J, hSS']
  exact hWreg S' hmem hS'J y (mem_iInter₂.1 hy S' hmem)

/-- The regular footprint `V_I = ψ_∅I(X_I^reg ∩ Z_∅I) ⊆ X`. -/
def footprint (I : Finset A) : Set X :=
  𝒜.baseHomeomorph '' (𝒜.footprintMap (Finset.empty_subset I) '' {x | x.val ∈ 𝒜.regLocus I})

@[simp]
theorem mem_footprint {I : Finset A} {y : X} :
    y ∈ 𝒜.footprint I ↔ ∃ x : kuranishiZeroSet 𝒜.kuranishi ∅ I,
      x.val ∈ 𝒜.regLocus I ∧ 𝒜.baseHomeomorph (𝒜.footprintMap (Finset.empty_subset I) x) = y := by
  simp [footprint]

/-- The regular footprint `V_I` is empty when the regular locus `X_I^reg` is. -/
theorem footprint_eq_empty_of_regLocus_eq_empty {I : Finset A} (h : 𝒜.regLocus I = ∅) :
    𝒜.footprint I = ∅ := by
  simp [footprint, h]

/-- The regular footprints are open. The set `X_I^reg ∩ Z_∅I` is open in `Z_∅I` and is a union
of fibres of `ψ_∅I`, so its image is open in `U_∅I` by the quotient axiom, and `U_∅I` is open in
`X_∅ ≃ₜ X`. -/
theorem isOpen_footprint (I : Finset A) : IsOpen (𝒜.footprint I) := by
  set ψ := 𝒜.footprintMap (Finset.empty_subset I)
  set W : Set (kuranishiZeroSet 𝒜.kuranishi ∅ I) := {x | x.val ∈ 𝒜.regLocus I}
  have hW : IsOpen W := (𝒜.isOpen_regLocus I).preimage continuous_subtypeVal
  -- `W` is saturated for `ψ`, so its image in `range ψ` is open.
  have hsat : rangeFactorization ψ ⁻¹' (rangeFactorization ψ '' W) = W := by
    refine Subset.antisymm (fun x ⟨y, hy, hyx⟩ ↦ ?_) (subset_preimage_image _ _)
    exact 𝒜.mem_regLocus_of_footprintMap_eq _ (congrArg Subtype.val hyx) hy
  have hopen : IsOpen (rangeFactorization ψ '' W) :=
    ((𝒜.isQuotientMap_footprintMap _).isOpen_preimage).1 (by rwa [hsat])
  have himage : ψ '' W = Subtype.val '' (rangeFactorization ψ '' W) := by
    simp only [image_image, rangeFactorization_coe]
  exact 𝒜.baseHomeomorph.isOpenMap _ (himage ▸
    (𝒜.isOpen_range_footprintMap _).isOpenMap_subtypeVal _ hopen)

/-- The regular footprints cover `X`. -/
theorem iUnion_footprint : ⋃ I, 𝒜.footprint I = univ :=
  eq_univ_of_forall fun y ↦ mem_iUnion.2 <|
    let ⟨I, x, hx, hxy⟩ := 𝒜.exists_footprintMap_eq y
    ⟨I, 𝒜.mem_footprint.2 ⟨x, hx, hxy⟩⟩

/-- A point of `Z_IJ` fixed by a nontrivial element of `Γ_(J \ I)` does not lie over the regular
locus of `X_I`: `Γ_(J \ I)` acts freely on `ψ_IJ⁻¹(X_I^reg)`. -/
theorem footprintMap_notMem_regLocus_of_act_eq {I J : Finset A} (h : I ⊆ J)
    (x : kuranishiZeroSet 𝒜.kuranishi I J) {g : (α : J) → Γ α} (hg : g ≠ 1)
    (hgI : Finset.restrict₂ (π := Γ) h g = 1) (hx : act J g x = x) :
    𝒜.footprintMap h x ∉ 𝒜.regLocus I :=
  fun hreg ↦ hg (𝒜.eq_one_of_act_eq h x hreg g hgI hx)

/-- **An ineffective point has no regular base.** Suppose that for some index `α` the obstruction
space `E_α` is zero, the thickenings `X_∅` and `X_α` are single points and the group `Γ_α` is
nontrivial, so that it acts on `X_α` ineffectively. Then the regular locus of `X_∅` is empty,
since `Γ_α` cannot act freely over `ψ_∅α⁻¹(X_∅^reg)`. -/
theorem regLocus_empty_eq_empty_of_nontrivial (α : A) [Nontrivial (Γ α)] [Subsingleton (E α)]
    [Subsingleton (T ∅)] [Subsingleton (T {α})] [Nonempty (T {α})] : 𝒜.regLocus ∅ = ∅ := by
  -- A nontrivial element of `Γ_α` fixes the point of `Z_∅α = X_α`, which `ψ_∅α` sends to the
  -- point of `X_∅`.
  refine eq_empty_of_forall_notMem fun y hy ↦ ?_
  obtain ⟨x⟩ := ‹Nonempty (T {α})›
  have hx : x ∈ kuranishiZeroSet 𝒜.kuranishi ∅ {α} := mem_kuranishiZeroSet.2 fun ⟨β, hβ⟩ _ ↦ by
    obtain rfl := Finset.mem_singleton.1 hβ
    exact Subsingleton.elim _ _
  obtain ⟨γ, hγ⟩ := exists_ne (1 : Γ α)
  refine 𝒜.footprintMap_notMem_regLocus_of_act_eq (Finset.empty_subset {α}) ⟨x, hx⟩
    (g := Pi.mulSingle (M := fun β : ({α} : Finset A) ↦ Γ β) ⟨α, Finset.mem_singleton_self α⟩ γ)
    (fun hg ↦ hγ (by simpa using congr_fun hg ⟨α, Finset.mem_singleton_self α⟩))
    (funext fun β ↦ (Finset.notMem_empty _ β.property).elim) (Subsingleton.elim _ _)
    (Subsingleton.elim y (𝒜.footprintMap _ ⟨x, hx⟩) ▸ hy)

/-! ### Footprint conditions -/

/-- The images of the footprint maps shrink as the larger index set grows: `U_IK ⊆ U_IJ` for
`I ⊆ J ⊆ K`, since `ψ_IK = ψ_IJ ∘ ψ_JK`. -/
theorem range_footprintMap_subset {I J K : Finset A} (hIJ : I ⊆ J) (hJK : J ⊆ K) :
    range (𝒜.footprintMap (hIJ.trans hJK)) ⊆ range (𝒜.footprintMap hIJ) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨_, 𝒜.footprintMap_footprintMap_mk hIJ hJK
    ⟨x.val, kuranishiZeroSet_mono _ hIJ K x.property⟩ x.property⟩

/-- The regular footprint `V_I` lies in the image `U_∅I` of the footprint map `ψ_∅I`. -/
theorem footprint_subset_image_range (I : Finset A) :
    𝒜.footprint I ⊆ 𝒜.baseHomeomorph '' range (𝒜.footprintMap (Finset.empty_subset I)) :=
  image_mono (image_subset_range _ _)

/-- A point of the zero set `Z_∅I` lies over the regular footprint `V_I` exactly when it is
regular: the fibres of `ψ_∅I` are `Γ_I`-orbits, and the regular locus is invariant. -/
theorem baseHomeomorph_footprintMap_mem_footprint_iff {I : Finset A}
    (x : kuranishiZeroSet 𝒜.kuranishi ∅ I) :
    𝒜.baseHomeomorph (𝒜.footprintMap (Finset.empty_subset I) x) ∈ 𝒜.footprint I ↔
      x.val ∈ 𝒜.regLocus I := by
  refine ⟨fun h ↦ ?_, fun h ↦ 𝒜.mem_footprint.2 ⟨x, h, rfl⟩⟩
  obtain ⟨y, hy, hyx⟩ := 𝒜.mem_footprint.1 h
  exact 𝒜.mem_regLocus_of_footprintMap_eq _ (𝒜.baseHomeomorph.injective hyx) hy

/-- For `I ⊆ J`, a point `x` of the zero set `Z_∅J` lies over the regular footprint `V_I` exactly
when its image `ψ_IJ(x)` is regular, since `ψ_∅J = ψ_∅I ∘ ψ_IJ`. -/
theorem baseHomeomorph_footprintMap_mem_footprint_iff_of_subset {I J : Finset A} (hIJ : I ⊆ J)
    (x : kuranishiZeroSet 𝒜.kuranishi ∅ J) :
    𝒜.baseHomeomorph (𝒜.footprintMap (Finset.empty_subset J) x) ∈ 𝒜.footprint I ↔
      𝒜.footprintMap hIJ ⟨x.val, kuranishiZeroSet_mono _ (Finset.empty_subset I) J x.property⟩ ∈
        𝒜.regLocus I := by
  rw [← 𝒜.footprintMap_footprintMap_mk (Finset.empty_subset I) hIJ
    ⟨x.val, kuranishiZeroSet_mono _ (Finset.empty_subset I) J x.property⟩ x.property,
    baseHomeomorph_footprintMap_mem_footprint_iff]

/-- For `I ⊆ K`, the regular footprint `V_I` meets the image `U_∅K` of `ψ_∅K` only inside `V_K`.
A zero `x ∈ Z_∅K` over `V_I` has a regular image `ψ_IK(x) ∈ X_I^reg`, so it is regular itself
by the axiom `ψ_IK⁻¹(X_I^reg) ⊆ X_K^reg`. -/
theorem footprint_inter_image_range_subset {I K : Finset A} (hIK : I ⊆ K) :
    𝒜.footprint I ∩ 𝒜.baseHomeomorph '' range (𝒜.footprintMap (Finset.empty_subset K)) ⊆
      𝒜.footprint K := by
  rintro _ ⟨hI, _, ⟨x, rfl⟩, rfl⟩
  exact (𝒜.baseHomeomorph_footprintMap_mem_footprint_iff x).2 (𝒜.mem_regLocus_of_footprintMap_mem
    hIK _ ((𝒜.baseHomeomorph_footprintMap_mem_footprint_iff_of_subset hIK x).1 hI))

/-- **The first footprint condition** (Pardon, proof of Proposition 4.3.3): `V_I ∩ V_K ⊆ V_J`
for `I ⊆ J ⊆ K`. The inclusion can be strict: for the atlas `s(x) = xᵐ` on a point, with
`I = ∅` and `J = K = {α}`, the left side is `V_∅ = ∅` while `V_{α}` is the point. -/
theorem footprint_inter_footprint_subset_footprint {I J K : Finset A} (hIJ : I ⊆ J)
    (hJK : J ⊆ K) : 𝒜.footprint I ∩ 𝒜.footprint K ⊆ 𝒜.footprint J :=
  fun _ ⟨hI, hK⟩ ↦ 𝒜.footprint_inter_image_range_subset hIJ ⟨hI, image_mono
    (𝒜.range_footprintMap_subset (Finset.empty_subset J) hJK) (𝒜.footprint_subset_image_range K hK)⟩

/-- **The second footprint condition** (Pardon, proof of Proposition 4.3.3):
`V_I ∩ V_J ⊆ V_(I ∪ J)`. -/
theorem footprint_inter_footprint_subset_footprint_union (I J : Finset A) :
    𝒜.footprint I ∩ 𝒜.footprint J ⊆ 𝒜.footprint (I ∪ J) := by
  rintro _ ⟨hI, hJ⟩
  refine 𝒜.footprint_inter_image_range_subset Finset.subset_union_left ⟨hI, ?_⟩
  rw [← 𝒜.range_footprintMap_inter (Finset.empty_subset I) (Finset.empty_subset J),
    image_inter 𝒜.baseHomeomorph.injective]
  exact ⟨𝒜.footprint_subset_image_range I hI, 𝒜.footprint_subset_image_range J hJ⟩

end Core

variable (𝒜 : ImplicitAtlas Γ E ρ T act X d)

/-- **Charts at regular points.** Every point of `X_I^reg` lies in the source of an open partial
homeomorphism from `X_I` to `ℝⁿ`, where the natural number `n` is the expected dimension
`d + m_I`. -/
theorem exists_openPartialHomeomorph_of_mem_regLocus {I : Finset A} {x : T I}
    (hx : x ∈ 𝒜.regLocus I) :
    ∃ n : ℕ, (n : ℤ) = d + ∑ α ∈ I, (Module.finrank ℝ (E α) : ℤ) ∧
      ∃ e : OpenPartialHomeomorph (T I) (EuclideanSpace ℝ (Fin n)), x ∈ e.source := by
  have hψ : 𝒜.footprintMap (subset_refl I) ⟨x, mem_kuranishiZeroSet_self _ x⟩ ∈ 𝒜.regLocus I := by
    rwa [𝒜.footprintMap_self]
  obtain ⟨n, hn, e, hxe, -⟩ := 𝒜.exists_openPartialHomeomorph (subset_refl I) _ hψ
  have : IsEmpty ↥(I \ I) := ⟨fun α ↦ by simpa using α.property⟩
  exact ⟨n, hn, e.transHomeomorph (Homeomorph.prodUnique _ _), hxe⟩

/-- The expected dimension `d + m_I` is nonnegative wherever the regular locus `X_I^reg` is
nonempty: there it is the dimension of a topological manifold. -/
theorem nonneg_of_mem_regLocus {I : Finset A} {x : T I} (hx : x ∈ 𝒜.regLocus I) :
    0 ≤ d + ∑ α ∈ I, (Module.finrank ℝ (E α) : ℤ) := by
  obtain ⟨n, hn, -⟩ := 𝒜.exists_openPartialHomeomorph_of_mem_regLocus hx
  exact hn ▸ Int.natCast_nonneg n

/-- The regular locus `X_I^reg` is empty when the expected dimension `d + m_I` is negative. -/
theorem regLocus_eq_empty_of_neg {I : Finset A}
    (hI : d + ∑ α ∈ I, (Module.finrank ℝ (E α) : ℤ) < 0) : 𝒜.regLocus I = ∅ :=
  eq_empty_of_forall_notMem fun _ hx ↦ (𝒜.nonneg_of_mem_regLocus hx).not_gt hI

include 𝒜 in
/-- A space carries no implicit atlas whose expected dimensions `d + m_I` are all negative,
unless it is empty: the regular footprints cover it, and they are empty. -/
theorem isEmpty_of_forall_neg
    (hd : ∀ I : Finset A, d + ∑ α ∈ I, (Module.finrank ℝ (E α) : ℤ) < 0) : IsEmpty X :=
  ⟨fun y ↦ by
    obtain ⟨I, x, hx, -⟩ := 𝒜.exists_footprintMap_eq y
    exact (𝒜.nonneg_of_mem_regLocus hx).not_gt (hd I)⟩

end ImplicitAtlas

end TauCeti
