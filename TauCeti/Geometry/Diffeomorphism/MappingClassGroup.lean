/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Path
public import TauCeti.Geometry.Diffeomorphism.FixingSubgroup.Topology
public import TauCeti.Geometry.Manifold.Orientation.Preserving

/-!
# The smooth mapping class group

For a compact Hausdorff smooth manifold `M`, possibly with boundary, the mapping class group
`Mod(M)` is the group of isotopy classes of smooth diffeomorphisms of `M` fixing `∂M` pointwise,
the isotopies fixing `∂M` pointwise throughout. Isotopies are taken in the weak Whitney topology:
two diffeomorphisms are isotopic when they are joined by a path in the relative diffeomorphism
group `Diff(M, ∂M)` (`TauCeti.RelativeDiff`), which is a topological group by
`Diffeomorph.isTopologicalGroup`. So `Mod(M)` is the quotient of `Diff(M, ∂M)` by the path
component of the identity, a normal subgroup, that is, the group `π₀ Diff(M, ∂M)`.

For an orientation `o` of `M`, `Mod⁺(M)` is the subgroup of classes of orientation-preserving
diffeomorphisms.

The definition is the same in every dimension; the classical case is that of compact connected
surfaces.

## Main definitions

* `TauCeti.MappingClassGroup I M`: the mapping class group `Mod(M)`.
* `TauCeti.MappingClassGroup.mk`: the quotient homomorphism `Diff(M, ∂M) →* Mod(M)`.
* `TauCeti.MappingClassGroup.lift`: a homomorphism out of `Diff(M, ∂M)` that is trivial on
  diffeomorphisms isotopic to the identity relative to `∂M` descends to `Mod(M)`.
* `TauCeti.MappingClassGroup.orientationPreserving o`: the subgroup `Mod⁺(M)`.

## Main results

* `TauCeti.MappingClassGroup.mk_surjective`: every mapping class has a representative.
* `TauCeti.MappingClassGroup.mk_eq_mk_iff`: two relative diffeomorphisms have the same class
  exactly when they are joined by a path in `Diff(M, ∂M)`.
* `TauCeti.MappingClassGroup.ker_mk`: the kernel of `mk` is the path component of the identity.
* `TauCeti.MappingClassGroup.lift_mk`, `TauCeti.MappingClassGroup.hom_ext`: the universal property
  of `mk`.
* `TauCeti.MappingClassGroup.mk_final_eq_one`: the final diffeomorphism of a diffeotopy fixing
  `∂M` pointwise at every time represents the trivial class.

## References

* B. Farb and D. Margalit, *A Primer on Mapping Class Groups*, Princeton University Press (2012),
  Section 2.1.
-/

public section

open scoped Manifold ContDiff TauCeti.DiffeomorphWeakWhitney

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace TauCeti

variable [CompactSpace M] [T2Space M]

variable (I M) in
/-- The smooth mapping class group `Mod(M)` of a compact manifold `M`, possibly with boundary:
the group of isotopy classes of smooth diffeomorphisms fixing `∂M` pointwise, an isotopy being a
path in the relative diffeomorphism group `Diff(M, ∂M)` with the weak Whitney topology. It is the
quotient of `Diff(M, ∂M)` by the path component of the identity. -/
def MappingClassGroup : Type _ :=
  RelativeDiff I M ∞ (I.boundary M) ⧸
    Subgroup.pathComponentOne (RelativeDiff I M ∞ (I.boundary M))

namespace MappingClassGroup

noncomputable instance : Group (MappingClassGroup I M) :=
  inferInstanceAs (Group (_ ⧸ Subgroup.pathComponentOne (RelativeDiff I M ∞ (I.boundary M))))

noncomputable instance : Inhabited (MappingClassGroup I M) := ⟨1⟩

variable (I M) in
/-- The quotient homomorphism sending a diffeomorphism fixing `∂M` pointwise to its mapping
class. -/
noncomputable def mk : RelativeDiff I M ∞ (I.boundary M) →* MappingClassGroup I M :=
  QuotientGroup.mk' _

/-- Every mapping class is the class of a diffeomorphism fixing `∂M` pointwise. -/
theorem mk_surjective : Function.Surjective (mk I M) :=
  QuotientGroup.mk'_surjective _

/-- The kernel of the quotient map is the path component of the identity in `Diff(M, ∂M)`. -/
@[simp]
theorem ker_mk : (mk I M).ker = Subgroup.pathComponentOne (RelativeDiff I M ∞ (I.boundary M)) :=
  QuotientGroup.ker_mk' _

/-- A diffeomorphism fixing `∂M` pointwise represents the trivial mapping class exactly when it
is isotopic to the identity relative to `∂M`. -/
theorem mk_eq_one_iff {f : RelativeDiff I M ∞ (I.boundary M)} : mk I M f = 1 ↔ Joined 1 f := by
  rw [← MonoidHom.mem_ker, ker_mk, ← SetLike.mem_coe, Subgroup.coe_pathComponentOne,
    mem_pathComponent_iff]

/-- Two diffeomorphisms fixing `∂M` pointwise have the same mapping class exactly when they are
isotopic relative to `∂M`. -/
theorem mk_eq_mk_iff {f g : RelativeDiff I M ∞ (I.boundary M)} :
    mk I M f = mk I M g ↔ Joined f g := by
  rw [← div_eq_one, ← map_div, mk_eq_one_iff, div_eq_mul_inv]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simpa using (h.map (f := (· * g)) (by fun_prop)).symm
  · simpa using (h.map (f := (· * g⁻¹)) (by fun_prop)).symm

section Lift

variable {G : Type*} [Group G]

/-- A homomorphism out of `Diff(M, ∂M)` that is trivial on every diffeomorphism isotopic to the
identity relative to `∂M` descends to the mapping class group. -/
noncomputable def lift (φ : RelativeDiff I M ∞ (I.boundary M) →* G)
    (hφ : ∀ f, Joined 1 f → φ f = 1) : MappingClassGroup I M →* G :=
  QuotientGroup.lift _ φ fun f hf => hφ f <| by
    rwa [← SetLike.mem_coe, Subgroup.coe_pathComponentOne, mem_pathComponent_iff] at hf

/-- The descended homomorphism sends the class of `f` to `φ f`. -/
@[simp]
theorem lift_mk (φ : RelativeDiff I M ∞ (I.boundary M) →* G) (hφ : ∀ f, Joined 1 f → φ f = 1)
    (f : RelativeDiff I M ∞ (I.boundary M)) : lift φ hφ (mk I M f) = φ f :=
  QuotientGroup.lift_mk' _ _ f

/-- The descended homomorphism composed with `mk` is `φ`. -/
@[simp]
theorem lift_comp_mk (φ : RelativeDiff I M ∞ (I.boundary M) →* G)
    (hφ : ∀ f, Joined 1 f → φ f = 1) : (lift φ hφ).comp (mk I M) = φ :=
  MonoidHom.ext (lift_mk φ hφ)

/-- Two homomorphisms out of the mapping class group agreeing on every class `mk I M f` are
equal. -/
@[ext]
theorem hom_ext {ψ ψ' : MappingClassGroup I M →* G}
    (h : ψ.comp (mk I M) = ψ'.comp (mk I M)) : ψ = ψ' :=
  QuotientGroup.monoidHom_ext _ h

/-- The descended homomorphism is the only one whose composite with `mk` is `φ`. -/
theorem eq_lift_iff {φ : RelativeDiff I M ∞ (I.boundary M) →* G}
    {hφ : ∀ f, Joined 1 f → φ f = 1} {ψ : MappingClassGroup I M →* G} :
    ψ = lift φ hφ ↔ ψ.comp (mk I M) = φ :=
  ⟨fun h => h ▸ lift_comp_mk φ hφ, fun h => hom_ext (h.trans (lift_comp_mk φ hφ).symm)⟩

end Lift

/-- The final diffeomorphism of a diffeotopy fixing `∂M` pointwise at every time represents the
trivial mapping class. -/
theorem mk_final_eq_one (Φ : Diffeotopy I ∞ M)
    (hΦ : ∀ t x, x ∈ I.boundary M → Φ (t, x) = x) :
    mk I M ⟨Φ.final, Diffeomorph.mem_fixingSubgroup_of_forall fun x hx =>
      (Φ.final_apply x).trans (hΦ 1 x hx)⟩ = 1 :=
  mk_eq_one_iff.mpr (JoinedIn.joined_subtype ⟨Φ.toPath, fun t =>
    Diffeomorph.mem_fixingSubgroup_of_forall fun x hx =>
      (DFunLike.congr_fun (Φ.toPath_apply t) x).trans ((Φ.timeSlice_apply t x).trans (hΦ t x hx))⟩)

section Orientation

variable {ι : Type*} [Fintype ι]

/-- For an orientation `o` of `M`, the subgroup `Mod⁺(M)` of mapping classes of
orientation-preserving diffeomorphisms fixing `∂M` pointwise. -/
noncomputable def orientationPreserving (o : Manifold.Orientation I M ι) :
    Subgroup (MappingClassGroup I M) :=
  (Diffeomorph.orientationPreservingSubgroup o).subgroupOf
    (fixingSubgroup (Diff I M ∞) (I.boundary M)) |>.map (mk I M)

/-- A mapping class lies in `Mod⁺(M)` when it has an orientation-preserving representative. -/
theorem mem_orientationPreserving_iff {o : Manifold.Orientation I M ι}
    {φ : MappingClassGroup I M} :
    φ ∈ orientationPreserving o ↔ ∃ f : RelativeDiff I M ∞ (I.boundary M),
      (∀ x, Manifold.Orientation.IsOrientationPreservingAt o o (f : Diff I M ∞) x) ∧
        mk I M f = φ := by
  simp [orientationPreserving, Subgroup.mem_subgroupOf]

/-- The class of an orientation-preserving diffeomorphism fixing `∂M` lies in `Mod⁺(M)`. -/
theorem mk_mem_orientationPreserving {o : Manifold.Orientation I M ι}
    {f : RelativeDiff I M ∞ (I.boundary M)}
    (hf : ∀ x, Manifold.Orientation.IsOrientationPreservingAt o o (f : Diff I M ∞) x) :
    mk I M f ∈ orientationPreserving o :=
  mem_orientationPreserving_iff.mpr ⟨f, hf, rfl⟩

end Orientation

end MappingClassGroup

end TauCeti
