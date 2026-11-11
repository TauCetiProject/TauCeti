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

This is the mapping class group of the geometric-topology roadmap, where it is studied for compact
connected surfaces; the definition is the same in every dimension.

## Main definitions

* `TauCeti.MappingClassGroup I M`: the mapping class group `Mod(M)`.
* `TauCeti.MappingClassGroup.mk`: the quotient homomorphism `Diff(M, ∂M) →* Mod(M)`.
* `Diffeomorph.orientationPreservingSubgroup o`: the diffeomorphisms preserving `o` at every point.
* `TauCeti.MappingClassGroup.orientationPreserving o`: the subgroup `Mod⁺(M)`.

## Main results

* `TauCeti.MappingClassGroup.mk_surjective`: every mapping class has a representative.
* `TauCeti.MappingClassGroup.mk_eq_mk_iff`: two relative diffeomorphisms have the same class
  exactly when they are joined by a path in `Diff(M, ∂M)`.
* `TauCeti.MappingClassGroup.ker_mk`: the kernel of `mk` is the path component of the identity.
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

namespace Diffeomorph

variable {ι : Type*} [Fintype ι]

/-- The subgroup of smooth self-diffeomorphisms of `M` preserving the orientation `o` at every
point. -/
def orientationPreservingSubgroup (o : TauCeti.Manifold.Orientation I M ι) :
    Subgroup (TauCeti.Diff I M ∞) where
  carrier := {f | ∀ x, TauCeti.Manifold.Orientation.IsOrientationPreservingAt o o f x}
  mul_mem' {f g} hf hg x := by
    rw [coe_mul]
    exact (hf (g x)).comp (hg x)
  one_mem' x := TauCeti.Manifold.Orientation.isOrientationPreservingAt_id o x
  inv_mem' {f} hf y := by
    rw [coe_inv]
    exact (hf (f.symm y)).diffeomorph_symm (by simp)

/-- Membership in the orientation-preserving subgroup is preservation of `o` at every point. -/
@[simp]
theorem mem_orientationPreservingSubgroup_iff {o : TauCeti.Manifold.Orientation I M ι}
    {f : TauCeti.Diff I M ∞} :
    f ∈ orientationPreservingSubgroup o ↔
      ∀ x, TauCeti.Manifold.Orientation.IsOrientationPreservingAt o o f x :=
  Iff.rfl

end Diffeomorph

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
  rw [← MonoidHom.mem_ker, ker_mk]
  exact Iff.rfl

/-- Two diffeomorphisms fixing `∂M` pointwise have the same mapping class exactly when they are
isotopic relative to `∂M`. -/
theorem mk_eq_mk_iff {f g : RelativeDiff I M ∞ (I.boundary M)} :
    mk I M f = mk I M g ↔ Joined f g := by
  refine (QuotientGroup.eq (s := Subgroup.pathComponentOne _)).trans ⟨fun h => ?_, fun h => ?_⟩
  · simpa using (show Joined 1 (f⁻¹ * g) from h).map (f := (f * ·)) (by fun_prop)
  · exact (by simpa using h.map (f := (f⁻¹ * ·)) (by fun_prop) : Joined 1 (f⁻¹ * g))

/-- The final diffeomorphism of a diffeotopy fixing `∂M` pointwise at every time represents the
trivial mapping class. -/
theorem mk_final_eq_one (Φ : Diffeotopy I ∞ M)
    (hΦ : ∀ t x, x ∈ I.boundary M → Φ (t, x) = x) :
    mk I M ⟨Φ.final, Diffeomorph.mem_fixingSubgroup_of_forall fun x hx =>
      (Φ.final_apply x).trans (hΦ 1 x hx)⟩ = 1 := by
  refine mk_eq_one_iff.mpr ⟨?_⟩
  refine ⟨⟨fun t => ⟨Φ.timeSlice t, Diffeomorph.mem_fixingSubgroup_of_forall fun x hx =>
      (Φ.timeSlice_apply t x).trans (hΦ t x hx)⟩,
    Φ.continuous_timeSlice.subtype_mk _⟩, ?_, ?_⟩
  · exact Subtype.ext (Φ.timeSlice_zero.trans Diffeomorph.one_def.symm)
  · exact Subtype.ext (Φ.final_def.symm)

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
