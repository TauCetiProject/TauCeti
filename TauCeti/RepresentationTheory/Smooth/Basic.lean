/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Stabilizer
public import TauCeti.RepresentationTheory.Subrepresentation
public import TauCeti.Topology.Algebra.Nonarchimedean.LocallyProfinite
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.NumberTheory.Padics.ProperSpace
import TauCeti.GroupTheory.QuotientGroup.Basic
import TauCeti.NumberTheory.Padics.QuotientTower

/-!
# Smooth representations and smooth vectors

Let `G` be a group equipped with a topology and `ρ : Representation A G V` a representation of `G`
on an `A`-module `V`, with no topology on `A` or `V`. The representation `ρ` is *smooth*
(`Representation.IsSmooth`) if for every `v : V` its stabilizer
`ρ.stabilizer v = {g : G | ρ g v = v}` is open in `G`. Unlike `TauCeti.IsSmoothDiscrete` (which
works on bundled continuous representations `TopRep R G` over topological modules),
`Representation.IsSmooth` sits directly on Mathlib's algebraic `Representation A G V`.

When `G` has separately continuous multiplication (`SeparatelyContinuousMul G`, satisfied in
particular by every topological group `IsTopologicalGroup G`), open subgroups are upwards-closed
and closed under conjugation (`Representation.isOpen_stabilizer_add`,
`Representation.isOpen_stabilizer_smul`, `Representation.isOpen_stabilizer_apply`). Consequently:

* `ρ` is smooth if and only if every vector is fixed by some open subgroup
  (`Representation.isSmooth_iff_exists_openSubgroup_le_stabilizer`);
* the vectors with open stabilizer form a subrepresentation `ρ.smoothVectors`
  (`Representation.smoothVectors`), which is smooth (`Representation.instIsSmoothSmoothVectors`)
  and is the largest smooth subrepresentation of `ρ`
  (`Subrepresentation.le_smoothVectors_iff_isSmooth`), with `ρ.smoothVectors = ⊤ ↔ ρ.IsSmooth`
  (`Representation.smoothVectors_eq_top_iff`);
* intertwining maps carry smooth vectors to smooth vectors and restrict to `smoothVectors`
  (`Representation.IntertwiningMap.restrictSmoothVectors`);
* subrepresentations, quotients, finite products, restrictions along continuous homomorphisms,
  descents along normal subgroups acting trivially, and coset permutation representations
  `A[G ⧸ U]` for open subgroups `U` are smooth.

When `A` is a commutative ring and `G` is locally profinite (locally compact, Hausdorff, and
totally disconnected), van Dantzig's theorem refines open stabilizers to compact open subgroups:
`ρ.smoothVectors` is the union (and supremum) of the invariant submodules `V^U` as `U` ranges over
compact open subgroups of `G` (`Representation.coe_smoothVectors_eq_biUnion_invariants_isCompact`,
`Representation.toSubmodule_smoothVectors_eq_biSup_invariants_isCompact`), and `ρ` is smooth if and
only if `V = ⋃_U V^U` over compact open `U`
(`Representation.biUnion_invariants_isCompact_eq_univ_iff_isSmooth`).

## Main definitions

* `Representation.IsSmooth`: open-stabilizer smoothness predicate class on `Representation A G V`.
* `Representation.smoothVectors`: the subrepresentation `V^∞` of vectors with open stabilizer.
* `Representation.IntertwiningMap.restrictSmoothVectors`: restriction of an intertwining map to
  `smoothVectors`.

## Main results

* `Representation.isSmooth_iff_exists_openSubgroup_le_stabilizer`
* `Subrepresentation.instIsSmoothToRepresentation` and `Subrepresentation.instIsSmoothQuotient`
* `Representation.instIsSmoothOfMulActionQuotient`
* `Representation.isSmooth_leftRegular_iff_discreteTopology` and
  `Representation.smoothVectors_leftRegular_eq_bot`
* `Representation.smoothVectors_eq_top_iff` and `Subrepresentation.le_smoothVectors_iff_isSmooth`
* `Representation.mem_smoothVectors_iff_exists_isCompact_openSubgroup`,
  `Representation.coe_smoothVectors_eq_biUnion_invariants_isCompact`, and
  `Representation.isSmooth_iff_forall_exists_isCompact_openSubgroup_mem_invariants`

## References

* J. N. Bernstein, *Representations of p-adic groups*, Harvard lecture notes by K. E. Rumelhart
  (1992), Chapter I, §1.1, Definition 2 and Proposition 1, p. 7.
-/

public section

open scoped MonoidAlgebra

namespace Representation

section Semiring

variable {A G V W : Type*} [Semiring A] [Group G] [TopologicalSpace G]
  [AddCommMonoid V] [Module A V] [AddCommMonoid W] [Module A W]

/-! ### Smooth representations -/

/-- A representation `ρ : Representation A G V` is **smooth** if every vector `v : V` has open
stabilizer `{g : G | ρ g v = v}` in `G`. -/
class IsSmooth (ρ : Representation A G V) : Prop where
  /-- Every vector has open stabilizer in `G`. -/
  isOpen_stabilizer (v : V) : IsOpen ((ρ.stabilizer v : Subgroup G) : Set G)

/-- In a smooth representation, every vector has open stabilizer. -/
theorem isOpen_stabilizer (ρ : Representation A G V) [ρ.IsSmooth] (v : V) :
    IsOpen ((ρ.stabilizer v : Subgroup G) : Set G) :=
  IsSmooth.isOpen_stabilizer v

/-- `ρ` is smooth if and only if every vector has open stabilizer. -/
theorem isSmooth_iff (ρ : Representation A G V) :
    ρ.IsSmooth ↔ ∀ v : V, IsOpen ((ρ.stabilizer v : Subgroup G) : Set G) :=
  ⟨fun h ↦ h.isOpen_stabilizer, fun h ↦ ⟨h⟩⟩

/-- In a smooth representation, every vector is fixed by an open subgroup (namely its own
stabilizer). -/
theorem IsSmooth.exists_openSubgroup_le_stabilizer {ρ : Representation A G V} [ρ.IsSmooth]
    (v : V) : ∃ U : OpenSubgroup G, U.toSubgroup ≤ ρ.stabilizer v :=
  ⟨⟨ρ.stabilizer v, ρ.isOpen_stabilizer v⟩, le_rfl⟩

/-- If multiplication in `G` is separately continuous and every vector is fixed by some open
subgroup, then `ρ` is smooth. -/
theorem isSmooth_of_exists_openSubgroup_le_stabilizer [SeparatelyContinuousMul G]
    {ρ : Representation A G V}
    (h : ∀ v : V, ∃ U : OpenSubgroup G, U.toSubgroup ≤ ρ.stabilizer v) :
    ρ.IsSmooth :=
  ⟨fun v ↦ let ⟨_, hU⟩ := h v; Subgroup.isOpen_of_openSubgroup (ρ.stabilizer v) hU⟩

/-- When `G` has separately continuous multiplication, `ρ` is smooth if and only if every vector is
fixed by some open subgroup of `G`. -/
theorem isSmooth_iff_exists_openSubgroup_le_stabilizer [SeparatelyContinuousMul G]
    (ρ : Representation A G V) :
    ρ.IsSmooth ↔ ∀ v : V, ∃ U : OpenSubgroup G, U.toSubgroup ≤ ρ.stabilizer v :=
  ⟨fun _ ↦ IsSmooth.exists_openSubgroup_le_stabilizer,
    isSmooth_of_exists_openSubgroup_le_stabilizer⟩

/-! ### Closure properties and basic instances -/

/-- Every representation of a discrete group is smooth. -/
instance instIsSmoothOfDiscreteTopology [DiscreteTopology G] (ρ : Representation A G V) :
    ρ.IsSmooth where
  isOpen_stabilizer _ := isOpen_discrete _

/-- Every trivial representation is smooth. -/
instance instIsSmoothOfIsTrivial (ρ : Representation A G V) [ρ.IsTrivial] : ρ.IsSmooth where
  isOpen_stabilizer v := by
    rw [ρ.stabilizer_eq_top v]
    exact isOpen_univ

/-- Any representation on a subsingleton module is smooth. -/
instance instIsSmoothOfSubsingleton [Subsingleton V] (ρ : Representation A G V) : ρ.IsSmooth where
  isOpen_stabilizer v := by
    rw [ρ.stabilizer_eq_top_of_subsingleton v]
    exact isOpen_univ

/-- **Every subrepresentation of a smooth representation is smooth.** -/
instance _root_.Subrepresentation.instIsSmoothToRepresentation {ρ : Representation A G V}
    [ρ.IsSmooth] (S : Subrepresentation ρ) : S.toRepresentation.IsSmooth where
  isOpen_stabilizer v := by
    rw [S.stabilizer_toRepresentation v]
    exact ρ.isOpen_stabilizer v

/-- Smoothness pulls back along an injective intertwining map. -/
theorem IsSmooth.of_injective_intertwiningMap {ρ : Representation A G V}
    {σ : Representation A G W} [σ.IsSmooth] (f : ρ.IntertwiningMap σ) (hf : Function.Injective f) :
    ρ.IsSmooth where
  isOpen_stabilizer v := by
    rw [← f.stabilizer_eq_of_injective hf v]
    exact σ.isOpen_stabilizer (f v)

/-- Equivalent representations are simultaneously smooth. -/
theorem Equiv.isSmooth_iff {ρ : Representation A G V} {σ : Representation A G W}
    (e : ρ.Equiv σ) : ρ.IsSmooth ↔ σ.IsSmooth :=
  ⟨fun _ ↦ .of_injective_intertwiningMap e.symm.toIntertwiningMap e.symm.injective,
    fun _ ↦ .of_injective_intertwiningMap e.toIntertwiningMap e.injective⟩

/-- Restricting a smooth representation along a continuous group homomorphism produces a smooth
representation. -/
theorem IsSmooth.comp {H : Type*} [Group H] [TopologicalSpace H] {ρ : Representation A G V}
    [ρ.IsSmooth] {f : H →* G} (hf : Continuous f) : IsSmooth (ρ.comp f) where
  isOpen_stabilizer v := (ρ.isOpen_stabilizer v).preimage hf

/-- Restricting a smooth representation to a subgroup (with the subspace topology) yields a smooth
representation. -/
instance instIsSmoothCompSubtype {ρ : Representation A G V} [ρ.IsSmooth] (H : Subgroup G) :
    IsSmooth (ρ.comp H.subtype) :=
  IsSmooth.comp continuous_subtype_val

/-- Descending a smooth representation to `G ⧸ S` along a normal subgroup `S` acting trivially
yields a smooth representation of `G ⧸ S` in the quotient topology. -/
instance instIsSmoothOfQuotient {ρ : Representation A G V} [ρ.IsSmooth] (S : Subgroup G)
    [S.Normal] [IsTrivial (ρ.comp S.subtype)] : (ρ.ofQuotient S).IsSmooth where
  isOpen_stabilizer v := by
    rw [← (QuotientGroup.isQuotientMap_mk S).isOpen_preimage]
    have hpre :
        (QuotientGroup.mk : G → G ⧸ S) ⁻¹' (((ρ.ofQuotient S).stabilizer v : Subgroup (G ⧸ S)) :
          Set (G ⧸ S)) = ((ρ.stabilizer v : Subgroup G) : Set G) := by
      ext g
      simp [ofQuotient_coe_apply]
    rw [hpre]
    exact ρ.isOpen_stabilizer v

/-- The binary product of two smooth representations is smooth. -/
instance instIsSmoothProd (ρ : Representation A G V) (σ : Representation A G W)
    [ρ.IsSmooth] [σ.IsSmooth] : (ρ.prod σ).IsSmooth where
  isOpen_stabilizer x := by
    rw [stabilizer_prod]
    exact (ρ.isOpen_stabilizer x.1).inter (σ.isOpen_stabilizer x.2)

/-- A finite product `Representation.pi ρ` of smooth representations is smooth. -/
instance instIsSmoothPi {ι : Type*} [Finite ι] {M : ι → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module A (M i)] (ρ : ∀ i, Representation A G (M i))
    [∀ i, (ρ i).IsSmooth] : (Representation.pi ρ).IsSmooth where
  isOpen_stabilizer x := by
    rw [stabilizer_pi, Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun i ↦ (ρ i).isOpen_stabilizer (x i)

/-- Smoothness pushes forward along a surjective intertwining map when `G` has separately
continuous multiplication. -/
theorem IntertwiningMap.isSmooth_of_surjective [SeparatelyContinuousMul G]
    {ρ : Representation A G V} {σ : Representation A G W} [ρ.IsSmooth]
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f) : σ.IsSmooth where
  isOpen_stabilizer w := by
    obtain ⟨v, rfl⟩ := hf w
    exact Subgroup.isOpen_mono (f.stabilizer_le v) (ρ.isOpen_stabilizer v)

/-! ### Stabilizer openness and the subrepresentation of smooth vectors -/

/-- The zero vector has open stabilizer in any representation. -/
theorem isOpen_stabilizer_zero (ρ : Representation A G V) :
    IsOpen ((ρ.stabilizer 0 : Subgroup G) : Set G) := by
  rw [ρ.stabilizer_zero]
  exact isOpen_univ

/-- Scalar multiplication preserves openness of vector stabilizers when `G` has separately
continuous multiplication. -/
theorem isOpen_stabilizer_smul [SeparatelyContinuousMul G] (ρ : Representation A G V) (c : A)
    {v : V} (hv : IsOpen ((ρ.stabilizer v : Subgroup G) : Set G)) :
    IsOpen ((ρ.stabilizer (c • v) : Subgroup G) : Set G) :=
  Subgroup.isOpen_mono (ρ.le_stabilizer_smul c v) hv

/-- Addition preserves openness of vector stabilizers when `G` has separately continuous
multiplication. -/
theorem isOpen_stabilizer_add [SeparatelyContinuousMul G] (ρ : Representation A G V) {v w : V}
    (hv : IsOpen ((ρ.stabilizer v : Subgroup G) : Set G))
    (hw : IsOpen ((ρ.stabilizer w : Subgroup G) : Set G)) :
    IsOpen ((ρ.stabilizer (v + w) : Subgroup G) : Set G) :=
  Subgroup.isOpen_mono (ρ.le_stabilizer_add v w) (hv.inter hw)

/-- Group translation preserves openness of vector stabilizers when `G` has separately continuous
multiplication: `ρ.stabilizer (ρ g v)` is the preimage of `ρ.stabilizer v` under the continuous
conjugation `x ↦ g⁻¹ * x * g`. -/
theorem isOpen_stabilizer_apply [SeparatelyContinuousMul G] (ρ : Representation A G V) (g : G)
    {v : V} (hv : IsOpen ((ρ.stabilizer v : Subgroup G) : Set G)) :
    IsOpen ((ρ.stabilizer (ρ g v) : Subgroup G) : Set G) := by
  rw [ρ.stabilizer_conj, Subgroup.map_equiv_eq_comap_symm, Subgroup.coe_comap]
  exact hv.preimage (((continuous_mul_const g).comp (continuous_const_mul g⁻¹)).congr fun x ↦ by
    simp [MulAut.conj_symm_apply])

/-- **The subrepresentation of smooth vectors** `V^∞`: the vectors of `V` whose stabilizer in `G`
is open. Separate continuity of multiplication in `G` (satisfied by every `IsTopologicalGroup G`)
closes open stabilizers under addition, scalar multiplication, and translation by `G`. -/
def smoothVectors [SeparatelyContinuousMul G] (ρ : Representation A G V) :
    Subrepresentation ρ where
  toSubmodule :=
    { carrier := {v : V | IsOpen ((ρ.stabilizer v : Subgroup G) : Set G)}
      zero_mem' := ρ.isOpen_stabilizer_zero
      add_mem' := ρ.isOpen_stabilizer_add
      smul_mem' c _ hv := ρ.isOpen_stabilizer_smul c hv }
  apply_mem_toSubmodule g _ hv := ρ.isOpen_stabilizer_apply g hv

/-- A vector lies in `ρ.smoothVectors` if and only if its stabilizer in `G` is open. -/
@[simp, grind =]
theorem mem_smoothVectors_iff [SeparatelyContinuousMul G] {ρ : Representation A G V} {v : V} :
    v ∈ ρ.smoothVectors ↔ IsOpen ((ρ.stabilizer v : Subgroup G) : Set G) :=
  (Iff.rfl)

/-- The carrier set of `ρ.smoothVectors` consists of the vectors with open stabilizer in `G`. -/
theorem coe_smoothVectors [SeparatelyContinuousMul G] (ρ : Representation A G V) :
    (ρ.smoothVectors : Set V) = {v : V | IsOpen ((ρ.stabilizer v : Subgroup G) : Set G)} :=
  (rfl)

/-- A vector lies in `ρ.smoothVectors` if and only if it is fixed by some open subgroup of `G`. -/
theorem mem_smoothVectors_iff_exists_openSubgroup [SeparatelyContinuousMul G]
    {ρ : Representation A G V} {v : V} :
    v ∈ ρ.smoothVectors ↔ ∃ U : OpenSubgroup G, U.toSubgroup ≤ ρ.stabilizer v := by
  rw [mem_smoothVectors_iff]
  exact ⟨fun hv ↦ ⟨⟨ρ.stabilizer v, hv⟩, le_rfl⟩,
    fun ⟨_, hU⟩ ↦ Subgroup.isOpen_of_openSubgroup (ρ.stabilizer v) hU⟩

/-- Over a commutative semiring `A`, `ρ.smoothVectors` coincides with the `A[G]`-submodule of
`ρ.asModule` generated by the vectors with open stabilizer: since vectors with open stabilizer are
already closed under `0`, `+`, scalar multiplication, and `G`-translation, their `A[G]`-span adds no
new elements. -/
theorem smoothVectors_eq_ofSubmodule'_span {R : Type*} [CommSemiring R]
    [SeparatelyContinuousMul G] [Module R V] (ρ : Representation R G V) :
    ρ.smoothVectors = Subrepresentation.ofSubmodule'
      (Submodule.span R[G]
        {v : ρ.asModule | IsOpen ((ρ.stabilizer (ρ.asModuleEquiv v) : Subgroup G) : Set G)}) := by
  have hset :
      {w : ρ.asModule | IsOpen ((ρ.stabilizer (ρ.asModuleEquiv w) : Subgroup G) : Set G)} =
        (ρ.smoothVectors.asSubmodule : Set ρ.asModule) := by
    ext w
    exact (mem_smoothVectors_iff (ρ := ρ) (v := ρ.asModuleEquiv w)).symm.trans
      (Subrepresentation.mem_asSubmodule_iff (σ := ρ.smoothVectors) (v := ρ.asModuleEquiv w)).symm
  rw [hset, Submodule.span_eq]
  exact (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)).symm_apply_apply
    ρ.smoothVectors

/-- **The restriction of any representation to its smooth vectors is smooth.** -/
instance instIsSmoothSmoothVectors [SeparatelyContinuousMul G] (ρ : Representation A G V) :
    ρ.smoothVectors.toRepresentation.IsSmooth where
  isOpen_stabilizer v := by
    rw [ρ.smoothVectors.stabilizer_toRepresentation v]
    exact mem_smoothVectors_iff.mp v.2

/-- **Universal property of `smoothVectors`:** a subrepresentation `S` of `ρ` is contained in
`ρ.smoothVectors` if and only if `S` is smooth. -/
@[simp]
theorem _root_.Subrepresentation.le_smoothVectors_iff_isSmooth [SeparatelyContinuousMul G]
    {ρ : Representation A G V} (S : Subrepresentation ρ) :
    S ≤ ρ.smoothVectors ↔ S.toRepresentation.IsSmooth := by
  rw [isSmooth_iff]
  refine ⟨fun hS v ↦ ?_, fun hS v hv ↦ ?_⟩
  · rw [S.stabilizer_toRepresentation v]
    exact mem_smoothVectors_iff.mp (hS v.2)
  · simpa [S.stabilizer_toRepresentation ⟨v, hv⟩] using hS ⟨v, hv⟩

/-- `ρ.smoothVectors = ⊤` if and only if `ρ` is smooth. -/
@[simp]
theorem smoothVectors_eq_top_iff [SeparatelyContinuousMul G] (ρ : Representation A G V) :
    ρ.smoothVectors = ⊤ ↔ ρ.IsSmooth := by
  rw [eq_top_iff, isSmooth_iff]
  exact ⟨fun h v ↦ mem_smoothVectors_iff.mp (h _root_.trivial),
    fun h v _ ↦ mem_smoothVectors_iff.mpr (h v)⟩

/-- For a smooth representation `ρ`, `ρ.smoothVectors = ⊤`. -/
theorem smoothVectors_eq_top [SeparatelyContinuousMul G] (ρ : Representation A G V) [ρ.IsSmooth] :
    ρ.smoothVectors = ⊤ :=
  (smoothVectors_eq_top_iff ρ).mpr ‹_›

/-- Every intertwining map carries smooth vectors to smooth vectors. -/
theorem IntertwiningMap.apply_mem_smoothVectors [SeparatelyContinuousMul G]
    {ρ : Representation A G V} {σ : Representation A G W}
    (f : ρ.IntertwiningMap σ) {v : V} (hv : v ∈ ρ.smoothVectors) :
    f v ∈ σ.smoothVectors :=
  mem_smoothVectors_iff.mpr <|
    Subgroup.isOpen_mono (f.stabilizer_le v) (mem_smoothVectors_iff.mp hv)

/-- **Functoriality of smooth vectors:** an intertwining map `f : ρ → σ` restricts to an
intertwining map `ρ.smoothVectors → σ.smoothVectors`. -/
def IntertwiningMap.restrictSmoothVectors [SeparatelyContinuousMul G]
    {ρ : Representation A G V} {σ : Representation A G W} (f : ρ.IntertwiningMap σ) :
    ρ.smoothVectors.toRepresentation.IntertwiningMap σ.smoothVectors.toRepresentation :=
  (f.comp ρ.smoothVectors.subtype).codRestrict σ.smoothVectors fun v ↦ by
    simpa using f.apply_mem_smoothVectors (Subrepresentation.mem_toSubmodule.mp v.2)

/-- Coercing `f.restrictSmoothVectors v` to the ambient module evaluates `f` on `v`. -/
@[simp]
theorem IntertwiningMap.coe_restrictSmoothVectors_apply [SeparatelyContinuousMul G]
    {ρ : Representation A G V} {σ : Representation A G W} (f : ρ.IntertwiningMap σ)
    (v : ρ.smoothVectors.toSubmodule) :
    ((f.restrictSmoothVectors v : σ.smoothVectors.toSubmodule) : W) = f v := by
  simp [restrictSmoothVectors]

/-- Restricting the identity intertwining map to `smoothVectors` yields the identity. -/
@[simp]
theorem IntertwiningMap.restrictSmoothVectors_id [SeparatelyContinuousMul G]
    (ρ : Representation A G V) :
    (IntertwiningMap.id ρ).restrictSmoothVectors = IntertwiningMap.id _ :=
  IntertwiningMap.ext <| LinearMap.ext fun _ ↦ Subtype.ext <| by simp

/-- Restriction to `smoothVectors` commutes with composition of intertwining maps. -/
@[simp]
theorem IntertwiningMap.restrictSmoothVectors_comp [SeparatelyContinuousMul G]
    {U : Type*} [AddCommMonoid U] [Module A U]
    {ρ : Representation A G V} {σ : Representation A G W} {τ : Representation A G U}
    (g : σ.IntertwiningMap τ) (f : ρ.IntertwiningMap σ) :
    (g.comp f).restrictSmoothVectors = g.restrictSmoothVectors.comp f.restrictSmoothVectors :=
  IntertwiningMap.ext <| LinearMap.ext fun _ ↦ Subtype.ext <| by simp

/-! ### Permutation, regular, and infinite-product representations -/

/-- If every point of a `G`-set `X` has open stabilizer in `G`, then the permutation representation
`A[X]` is smooth. -/
theorem isSmooth_ofMulAction_of_forall_isOpen_stabilizer [SeparatelyContinuousMul G]
    {X : Type*} [MulAction G X]
    (h : ∀ x : X, IsOpen ((MulAction.stabilizer G x : Subgroup G) : Set G)) :
    (ofMulAction A G X).IsSmooth where
  isOpen_stabilizer v := by
    induction v using MonoidAlgebra.induction_linear with
    | zero => exact (ofMulAction A G X).isOpen_stabilizer_zero
    | add u w hu hw => exact (ofMulAction A G X).isOpen_stabilizer_add hu hw
    | single x a =>
      exact Subgroup.isOpen_mono (le_stabilizer_ofMulAction_single x a) (h x)

/-- **Smoothness of coset permutation modules:** for any open subgroup `U` of `G` (not necessarily
normal), the coset permutation representation `A[G ⧸ U]` is smooth. -/
instance instIsSmoothOfMulActionQuotient [SeparatelyContinuousMul G] (U : OpenSubgroup G) :
    (ofMulAction A G (G ⧸ U.toSubgroup)).IsSmooth := by
  refine isSmooth_ofMulAction_of_forall_isOpen_stabilizer fun q ↦ ?_
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
  have hpre : ((MulAction.stabilizer G (s : G ⧸ U.toSubgroup) : Subgroup G) : Set G) =
      (fun x : G ↦ s⁻¹ * x * s) ⁻¹' (U : Set G) := by
    ext x
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, TauCeti.smul_quotientGroup_mk_eq_self_iff]
    rfl
  rw [hpre]
  exact U.isOpen.preimage ((continuous_mul_const s).comp (continuous_const_mul s⁻¹))

/-- Over a nontrivial semiring `A`, the left regular representation `A[G]` is smooth if and only if
`G` carries the discrete topology. -/
@[simp]
theorem isSmooth_leftRegular_iff_discreteTopology [Nontrivial A] [SeparatelyContinuousMul G] :
    (leftRegular A G).IsSmooth ↔ DiscreteTopology G := by
  refine ⟨fun h ↦ discreteTopology_of_isOpen_singleton_one ?_, fun _ ↦ inferInstance⟩
  have hopen := h.isOpen_stabilizer (MonoidAlgebra.single (1 : G) (1 : A))
  rw [stabilizer_leftRegular_single 1 one_ne_zero] at hopen
  exact hopen

/-- **In a non-discrete `T₁` group, the left regular representation has no nonzero smooth
vectors.** Every nonzero element of `A[G]` has finite stabilizer, which in a `T₁` space cannot be
open unless `{1}` is open. -/
theorem smoothVectors_leftRegular_eq_bot [SeparatelyContinuousMul G] [T1Space G]
    (hG : ¬ DiscreteTopology G) :
    (leftRegular A G).smoothVectors = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  by_contra hx0
  have hfin : ((leftRegular A G).stabilizer x : Set G).Finite := finite_stabilizer_leftRegular hx0
  have hopen : IsOpen ((leftRegular A G).stabilizer x : Set G) := mem_smoothVectors_iff.mp hx
  have hclosed : IsClosed (((leftRegular A G).stabilizer x : Set G) \ {1}) :=
    hfin.sdiff.isClosed
  have h1 : ({1} : Set G) =
      ((leftRegular A G).stabilizer x : Set G) ∩
        (((leftRegular A G).stabilizer x : Set G) \ {1})ᶜ := by
    ext g
    simp only [Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff, not_and,
      not_not]
    exact ⟨fun hg ↦ ⟨hg ▸ one_mem _, fun _ ↦ hg⟩, fun ⟨hg, h⟩ ↦ h hg⟩
  exact hG (discreteTopology_of_isOpen_singleton_one (h1 ▸ hopen.inter hclosed.isOpen_compl))

/-- In a product `∏ i, A[G ⧸ H i]` of coset permutation representations over a nontrivial
semiring `A`, if `⨅ i, H i` is not open in `G`, then the family of basepoints
`fun i ↦ single ↑1 1` is not a smooth vector. -/
theorem notMem_smoothVectors_pi_ofMulAction_quotient [Nontrivial A] [SeparatelyContinuousMul G]
    {ι : Type*} {H : ι → Subgroup G}
    (hH : ¬ IsOpen (((⨅ i, H i : Subgroup G) : Set G))) :
    (fun i ↦ MonoidAlgebra.single ((1 : G) : G ⧸ H i) 1) ∉
      (Representation.pi fun i ↦ ofMulAction A G (G ⧸ H i)).smoothVectors := by
  simpa [stabilizer_ofMulAction_single _ one_ne_zero] using hH

/-- In a product `∏ i, A[G ⧸ H i]` of coset permutation representations over a nontrivial
semiring `A`, if `⨅ i, H i` is not open in `G`, then the product representation is not smooth. -/
theorem not_isSmooth_pi_ofMulAction_quotient [Nontrivial A] {ι : Type*} {H : ι → Subgroup G}
    (hH : ¬ IsOpen (((⨅ i, H i : Subgroup G) : Set G))) :
    ¬ (Representation.pi fun i ↦ ofMulAction A G (G ⧸ H i)).IsSmooth := fun h ↦ by
  have hopen := h.isOpen_stabilizer (fun i ↦ MonoidAlgebra.single ((1 : G) : G ⧸ H i) 1)
  simp only [stabilizer_pi, stabilizer_ofMulAction_single _ one_ne_zero,
    MulAction.stabilizer_quotient] at hopen
  exact hH hopen

end Semiring

/-! ### Quotient representations -/

section Ring

variable {A G V : Type*} [Ring A] [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
  [AddCommGroup V] [Module A V]

/-- **Every quotient of a smooth representation by a subrepresentation is smooth.** -/
instance _root_.Subrepresentation.instIsSmoothQuotient {ρ : Representation A G V} [ρ.IsSmooth]
    (S : Subrepresentation ρ) : S.quotient.IsSmooth where
  isOpen_stabilizer q := by
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective S.toSubmodule q
    exact Subgroup.isOpen_mono (S.le_stabilizer_quotient_mk v) (ρ.isOpen_stabilizer v)

/-- **Every quotient representation `ρ.quotient W hW` of a smooth representation is smooth.** -/
instance instIsSmoothQuotient (ρ : Representation A G V) [ρ.IsSmooth] (W : Submodule A V)
    (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W) : (ρ.quotient W hW).IsSmooth :=
  Subrepresentation.instIsSmoothQuotient (S := ⟨W, hW⟩)

end Ring

/-! ### Subgroup invariants and locally profinite groups -/

section CommRing

variable {A G V : Type*} [CommRing A] [Group G] [TopologicalSpace G]
  [AddCommGroup V] [Module A V]

section TopologicalGroup

variable [SeparatelyContinuousMul G]

/-- Over a commutative ring, `v ∈ ρ.smoothVectors` if and only if `v ∈ V^U` for some open subgroup
`U` of `G`. -/
theorem mem_smoothVectors_iff_exists_openSubgroup_mem_invariants
    {ρ : Representation A G V} {v : V} :
    v ∈ ρ.smoothVectors ↔ ∃ U : OpenSubgroup G, v ∈ invariants (ρ.comp U.toSubgroup.subtype) := by
  simp_rw [mem_smoothVectors_iff_exists_openSubgroup, le_stabilizer_iff_mem_invariants_comp_subtype]

/-- Over a commutative ring, `ρ` is smooth if and only if every vector lies in `V^U` for some open
subgroup `U` of `G`. -/
theorem isSmooth_iff_forall_exists_openSubgroup_mem_invariants (ρ : Representation A G V) :
    ρ.IsSmooth ↔ ∀ v : V, ∃ U : OpenSubgroup G, v ∈ invariants (ρ.comp U.toSubgroup.subtype) := by
  simp_rw [isSmooth_iff_exists_openSubgroup_le_stabilizer,
    le_stabilizer_iff_mem_invariants_comp_subtype]

/-- As a set, `ρ.smoothVectors` is the union of the `U`-invariants `V^U` over all open subgroups
`U` of `G`. -/
theorem coe_smoothVectors_eq_iUnion_invariants (ρ : Representation A G V) :
    (ρ.smoothVectors : Set V) =
      ⋃ U : OpenSubgroup G, (invariants (ρ.comp U.toSubgroup.subtype) : Set V) := by
  ext v
  simp only [SetLike.mem_coe, mem_smoothVectors_iff_exists_openSubgroup_mem_invariants,
    Set.mem_iUnion]

/-- The underlying `A`-submodule of `ρ.smoothVectors` is the supremum of `V^U` over all open
subgroups `U` of `G`. -/
theorem toSubmodule_smoothVectors_eq_iSup_invariants (ρ : Representation A G V) :
    ρ.smoothVectors.toSubmodule =
      ⨆ U : OpenSubgroup G, invariants (ρ.comp U.toSubgroup.subtype) := by
  refine le_antisymm (fun v hv ↦ ?_) (iSup_le fun U v hv ↦ ?_)
  · obtain ⟨U, hU⟩ := mem_smoothVectors_iff_exists_openSubgroup_mem_invariants.mp hv
    exact Submodule.mem_iSup_of_mem U hU
  · exact mem_smoothVectors_iff_exists_openSubgroup_mem_invariants.mpr ⟨U, hv⟩

end TopologicalGroup

section LocallyProfinite

variable [IsTopologicalGroup G] [T2Space G] [WeaklyLocallyCompactSpace G]
  [TotallyDisconnectedSpace G]

/-- **Smooth vectors over a locally profinite group:** `v ∈ ρ.smoothVectors` if and only if `v` is
fixed by some *compact* open subgroup `U` of `G`. -/
theorem mem_smoothVectors_iff_exists_isCompact_openSubgroup {ρ : Representation A G V} {v : V} :
    v ∈ ρ.smoothVectors ↔
      ∃ U : OpenSubgroup G, IsCompact (U : Set G) ∧
        v ∈ invariants (ρ.comp U.toSubgroup.subtype) := by
  rw [mem_smoothVectors_iff_exists_openSubgroup]
  refine ⟨fun ⟨U₀, hU₀⟩ ↦ ?_, fun ⟨U, _, hU⟩ ↦
    ⟨U, (ρ.le_stabilizer_iff_mem_invariants_comp_subtype U.toSubgroup v).mpr hU⟩⟩
  obtain ⟨U, hUcpt, hUU₀⟩ := TauCeti.exists_isCompact_openSubgroup_le U₀
  exact ⟨U, hUcpt, (ρ.le_stabilizer_iff_mem_invariants_comp_subtype U.toSubgroup v).mp
    fun _ hg ↦ hU₀ (hUU₀ hg)⟩

/-- **Union of compact-open invariants:** for a locally profinite group `G`, the carrier of
`ρ.smoothVectors` is `⋃_U V^U` as `U` ranges over compact open subgroups of `G`. -/
theorem coe_smoothVectors_eq_biUnion_invariants_isCompact (ρ : Representation A G V) :
    (ρ.smoothVectors : Set V) =
      ⋃ (U : OpenSubgroup G) (_ : IsCompact (U : Set G)),
        (invariants (ρ.comp U.toSubgroup.subtype) : Set V) := by
  ext v
  simp only [SetLike.mem_coe, mem_smoothVectors_iff_exists_isCompact_openSubgroup, Set.mem_iUnion,
    exists_prop]

/-- For a locally profinite group `G`, the underlying `A`-submodule of `ρ.smoothVectors` is the
supremum of `V^U` over all compact open subgroups `U` of `G`. -/
theorem toSubmodule_smoothVectors_eq_biSup_invariants_isCompact (ρ : Representation A G V) :
    ρ.smoothVectors.toSubmodule =
      ⨆ (U : OpenSubgroup G) (_ : IsCompact (U : Set G)),
        invariants (ρ.comp U.toSubgroup.subtype) := by
  refine le_antisymm (fun v hv ↦ ?_) (iSup₂_le fun U hU v hv ↦ ?_)
  · obtain ⟨U, hUcpt, hU⟩ := mem_smoothVectors_iff_exists_isCompact_openSubgroup.mp hv
    exact Submodule.mem_iSup_of_mem U (Submodule.mem_iSup_of_mem hUcpt hU)
  · exact mem_smoothVectors_iff_exists_isCompact_openSubgroup.mpr ⟨U, hU, hv⟩

/-- **Smoothness over a locally profinite group:** `ρ` is smooth if and only if every vector lies
in `V^U` for some compact open subgroup `U` of `G`. -/
theorem isSmooth_iff_forall_exists_isCompact_openSubgroup_mem_invariants
    (ρ : Representation A G V) :
    ρ.IsSmooth ↔ ∀ v : V, ∃ U : OpenSubgroup G, IsCompact (U : Set G) ∧
      v ∈ invariants (ρ.comp U.toSubgroup.subtype) := by
  rw [← smoothVectors_eq_top_iff, eq_top_iff]
  refine ⟨fun h v ↦ mem_smoothVectors_iff_exists_isCompact_openSubgroup.mp (h _root_.trivial),
    fun h v _ ↦ mem_smoothVectors_iff_exists_isCompact_openSubgroup.mpr (h v)⟩

/-- For a locally profinite group `G`, `V = ⋃_U V^U` over compact open subgroups `U` if and only if
`ρ` is smooth. -/
theorem biUnion_invariants_isCompact_eq_univ_iff_isSmooth (ρ : Representation A G V) :
    (⋃ (U : OpenSubgroup G) (_ : IsCompact (U : Set G)),
      (invariants (ρ.comp U.toSubgroup.subtype) : Set V)) = Set.univ ↔ ρ.IsSmooth := by
  rw [← coe_smoothVectors_eq_biUnion_invariants_isCompact, ← smoothVectors_eq_top_iff]
  exact ⟨fun h ↦ SetLike.coe_injective (h.trans rfl), fun h ↦ h ▸ rfl⟩

/-- For a locally profinite group `G`, `⨆_U V^U = ⊤` over compact open subgroups `U` if and only if
`ρ` is smooth. -/
theorem biSup_invariants_isCompact_eq_top_iff_isSmooth (ρ : Representation A G V) :
    (⨆ (U : OpenSubgroup G) (_ : IsCompact (U : Set G)),
      invariants (ρ.comp U.toSubgroup.subtype)) = ⊤ ↔ ρ.IsSmooth := by
  rw [← toSubmodule_smoothVectors_eq_biSup_invariants_isCompact, ← smoothVectors_eq_top_iff,
    ← Subrepresentation.toSubmodule_injective.eq_iff, Subrepresentation.toSubmodule_top]

end LocallyProfinite

end CommRing

end Representation

end

/-! ### Concrete checks and counterexamples -/

section Examples

open Filter Set Topology Representation
open scoped MonoidAlgebra

-- Checks for `ℤ_p` (written multiplicatively via `Multiplicative ℤ_[p]`):
-- 1. `ℤ[ℤ_p]` is not smooth and its smooth vectors are `⊥`.
-- 2. `ℤ[ℤ_p ⧸ p^n ℤ_p]` is smooth and every vector is fixed by `p^n ℤ_p`.
-- 3. `∏_n ℤ[ℤ_p ⧸ p^n ℤ_p]` is not smooth, the family of basepoints not being smooth.
section PadicGroup

variable (p : ℕ) [Fact p.Prime]

example : ¬ (leftRegular ℤ (Multiplicative ℤ_[p])).IsSmooth ∧
    (leftRegular ℤ (Multiplicative ℤ_[p])).smoothVectors = ⊥ := by
  have hnd : ¬ DiscreteTopology (Multiplicative ℤ_[p]) := fun h ↦ by
    have : DiscreteTopology (Multiplicative ℤ_[p]) := h
    have : Finite (Multiplicative ℤ_[p]) := finite_of_compact_of_discrete
    have : Infinite (Multiplicative ℤ_[p]) := Infinite.of_injective
      (fun n : ℕ ↦ Multiplicative.ofAdd (n : ℤ_[p])) fun _ _ hab ↦
        Nat.cast_injective (Multiplicative.ofAdd.injective hab)
    exact _root_.not_finite (Multiplicative ℤ_[p])
  exact ⟨by simpa using hnd, smoothVectors_leftRegular_eq_bot hnd⟩

example (n : ℕ) :
    let U := ((TauCeti.FiniteQuotientTower.padicTower p).ker n).toOpenSubgroup
    (ofMulAction ℤ (Multiplicative ℤ_[p]) (Multiplicative ℤ_[p] ⧸ U.toSubgroup)).IsSmooth ∧
      ∀ v : ℤ[Multiplicative ℤ_[p] ⧸ U.toSubgroup],
        U.toSubgroup ≤
          (ofMulAction ℤ (Multiplicative ℤ_[p])
            (Multiplicative ℤ_[p] ⧸ U.toSubgroup)).stabilizer v :=
  ⟨inferInstance,
    le_stabilizer_ofMulAction_quotient
      ((TauCeti.FiniteQuotientTower.padicTower p).ker n).toSubgroup⟩

example :
    let H : ℕ → Subgroup (Multiplicative ℤ_[p]) :=
      fun n ↦ ((TauCeti.FiniteQuotientTower.padicTower p).ker n).toSubgroup
    ¬ (Representation.pi fun n ↦
        ofMulAction ℤ (Multiplicative ℤ_[p]) (Multiplicative ℤ_[p] ⧸ H n)).IsSmooth ∧
      (fun n ↦ MonoidAlgebra.single ((1 : Multiplicative ℤ_[p]) : Multiplicative ℤ_[p] ⧸ H n) 1) ∉
        (Representation.pi fun n ↦
          ofMulAction ℤ (Multiplicative ℤ_[p]) (Multiplicative ℤ_[p] ⧸ H n)).smoothVectors := by
  intro H
  have hnotOpen : ¬ IsOpen (((⨅ n, H n : Subgroup (Multiplicative ℤ_[p])) :
      Set (Multiplicative ℤ_[p]))) := by
    rw [(TauCeti.FiniteQuotientTower.padicTower p).iInf_ker_eq_bot]
    intro h1
    have : DiscreteTopology (Multiplicative ℤ_[p]) := discreteTopology_of_isOpen_singleton_one h1
    have : Finite (Multiplicative ℤ_[p]) := finite_of_compact_of_discrete
    have : Infinite (Multiplicative ℤ_[p]) := Infinite.of_injective
      (fun n : ℕ ↦ Multiplicative.ofAdd (n : ℤ_[p])) fun _ _ hab ↦
        Nat.cast_injective (Multiplicative.ofAdd.injective hab)
    exact _root_.not_finite (Multiplicative ℤ_[p])
  exact ⟨not_isSmooth_pi_ofMulAction_quotient hnotOpen,
    notMem_smoothVectors_pi_ofMulAction_quotient hnotOpen⟩

end PadicGroup

-- Check (discrete `G`): `V^∞ = ⊤` for every representation of a discrete group.
example {A G V : Type*} [Semiring A] [Group G] [TopologicalSpace G] [DiscreteTopology G]
    [AddCommMonoid V] [Module A V] (ρ : Representation A G V) :
    ρ.smoothVectors = ⊤ :=
  ρ.smoothVectors_eq_top

-- Check (topology): give `S₃` the topology generated by `H₀ = ⟨swap 0 1⟩`. In `ℚ[S₃ ⧸ H₀]`, the
-- basis vector at the identity coset has open stabilizer `H₀`, whereas its translate by
-- `swap 1 2` has stabilizer `conj (swap 1 2) • H₀`, which is not open. Thus an arbitrary topology
-- on `G` without continuity of multiplication does not yield a `G`-stable subset of vectors with
-- open stabilizer.
section BadTopologyS3

open Equiv

private abbrev s3Subgroup : Subgroup (Perm (Fin 3)) :=
  Subgroup.closure {swap (0 : Fin 3) 1}

private local instance : TopologicalSpace (Perm (Fin 3)) :=
  TopologicalSpace.generateFrom {(s3Subgroup : Set (Perm (Fin 3)))}

private theorem s3Subgroup_eq_stabilizer_two :
    s3Subgroup = MulAction.stabilizer (Perm (Fin 3)) (2 : Fin 3) := by
  refine le_antisymm ?_ fun σ hσ ↦ ?_
  · rw [Subgroup.closure_le, Set.singleton_subset_iff, SetLike.mem_coe,
      MulAction.mem_stabilizer_iff]
    decide
  · rw [MulAction.mem_stabilizer_iff] at hσ
    have hcases : σ = 1 ∨ σ = swap (0 : Fin 3) 1 := by
      decide +revert
    rcases hcases with rfl | rfl
    · exact one_mem _
    · exact Subgroup.subset_closure rfl

example :
    let ρ := ofMulAction ℚ (Perm (Fin 3)) (Perm (Fin 3) ⧸ s3Subgroup)
    let e₀ : ℚ[Perm (Fin 3) ⧸ s3Subgroup] :=
      MonoidAlgebra.single ((1 : Perm (Fin 3)) : Perm (Fin 3) ⧸ s3Subgroup) 1
    IsOpen ((ρ.stabilizer e₀ : Subgroup (Perm (Fin 3))) : Set (Perm (Fin 3))) ∧
      ¬ IsOpen ((ρ.stabilizer (ρ (swap 1 2) e₀) : Subgroup (Perm (Fin 3))) :
        Set (Perm (Fin 3))) := by
  intro ρ e₀
  refine ⟨?_, fun hopen ↦ ?_⟩
  · have he₀ : ρ.stabilizer e₀ = s3Subgroup := by
      simp [e₀, ρ, stabilizer_ofMulAction_single _ (one_ne_zero' ℚ)]
    rw [he₀]
    exact TopologicalSpace.isOpen_generateFrom_of_mem rfl
  · have htr : ρ (swap 1 2) e₀ = MonoidAlgebra.single
        ((swap (1 : Fin 3) 2 : Perm (Fin 3)) : Perm (Fin 3) ⧸ s3Subgroup) 1 := by
      simp [ρ, e₀]
    have hmem_iff (g : Perm (Fin 3)) :
        g ∈ ρ.stabilizer (ρ (swap 1 2) e₀) ↔
          (((swap (1 : Fin 3) 2)⁻¹ * g * swap 1 2 : Perm (Fin 3)) (2 : Fin 3)) = 2 := by
      rw [htr, stabilizer_ofMulAction_single _ (one_ne_zero' ℚ), MulAction.mem_stabilizer_iff,
        TauCeti.smul_quotientGroup_mk_eq_self_iff, s3Subgroup_eq_stabilizer_two,
        MulAction.mem_stabilizer_iff]
      rfl
    have h02 : swap (0 : Fin 3) 2 ∈ ρ.stabilizer (ρ (swap 1 2) e₀) :=
      (hmem_iff (swap 0 2)).mpr (by decide)
    have hnot02 : swap (0 : Fin 3) 2 ∉ (s3Subgroup : Set (Perm (Fin 3))) := by
      rw [SetLike.mem_coe, s3Subgroup_eq_stabilizer_two, MulAction.mem_stabilizer_iff]
      decide
    have hnhds : ((ρ.stabilizer (ρ (swap 1 2) e₀) : Subgroup (Perm (Fin 3))) :
        Set (Perm (Fin 3))) ∈ 𝓝 (swap (0 : Fin 3) 2) :=
      hopen.mem_nhds h02
    have htop : 𝓝 (swap (0 : Fin 3) 2) = ⊤ := by
      rw [TopologicalSpace.nhds_generateFrom, eq_top_iff]
      exact le_iInf₂ fun _ ⟨ha, hs⟩ ↦ (hnot02 (Set.mem_singleton_iff.mp hs ▸ ha)).elim
    rw [htop, Filter.mem_top] at hnhds
    have h12 : swap (1 : Fin 3) 2 ∈ ρ.stabilizer (ρ (swap 1 2) e₀) :=
      Set.eq_univ_iff_forall.mp hnhds (swap 1 2)
    exact absurd ((hmem_iff (swap 1 2)).mp h12) (by decide)

end BadTopologyS3

end Examples
