/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import TauCeti.RepresentationTheory.Continuous.InvariantComplement
public import TauCeti.RepresentationTheory.Continuous.StronglyContinuous
public import TauCeti.RepresentationTheory.Continuous.TopRep.KernelCokernel

/-!
# Kernel and cokernel representations of intertwining maps

Let a group `G` act on Hilbert spaces `E` and `F` by unitary representations `π` and `ρ` that are
only *strongly* continuous, as the translation actions on spaces of `L²` sections are, and let
`T : E → F` be a bounded operator intertwining them. The kernel of `T` is `π`-invariant and its
range is `ρ`-invariant, so `G` acts on the kernel and on the cokernel `F ⧸ range T`. This file shows
that when `T` is Fredholm these actions are *genuine* continuous finite-dimensional
representations, continuous for the operator norm and not only strongly continuous. These are the
two representations whose difference `[ker T] - [coker T]` is the equivariant index of `T`.

The continuity is the finite-dimensional upgrade of strong continuity, Mathlib's
`continuous_clm_apply`, applied to the kernel and to the quotient by
the closed range. It needs neither unitarity nor an inner product. When `ρ` is unitary the cokernel
is moreover identified, equivariantly and isometrically, with the orthogonal complement of the
closed range, a subrepresentation of `ρ` which is invariant because `ρ` is unitary. That complement
is the kernel of the adjoint, which intertwines `ρ` with `π`, so the cokernel representation is also
the kernel representation of the adjoint.

The kernel and cokernel actions are `ContIntertwiningMap.kerRepresentation` and
`ContIntertwiningMap.cokerRepresentation`, the representations underlying the objects `TopRep.ker`
and `TopRep.coker` of the category `TopRep`. Here they are studied as `ContRepresentation`s, the
carrier on which continuity for the operator norm and the comparison with the orthogonal complement
are stated.

## Main definitions

* `ContIntertwiningMap.orthogonalRangeRepresentation`: for a unitary target, the action on the
  orthogonal complement of the range.
* `ContIntertwiningMap.cokerEquivOrthogonalRange`: the equivalence of representations between the
  cokernel and the orthogonal complement of the range, when the range admits an orthogonal
  projection (for instance, when it is closed in a Hilbert space).
* `ContIntertwiningMap.cokerEquivKerAdjoint`: the equivalence of representations between the
  cokernel and the kernel of the adjoint, for unitary representations on Hilbert spaces.

## Main statements

* `ContIntertwiningMap.continuous_kerRepresentation`: a finite-dimensional kernel of an
  intertwining map out of a strongly continuous representation carries a continuous representation.
* `ContIntertwiningMap.continuous_cokerRepresentation`: likewise for a finite-dimensional cokernel
  of an intertwining map with closed range into a strongly continuous representation.
* `ContIntertwiningMap.continuous_kerRepresentation_of_isFredholm` and
  `ContIntertwiningMap.continuous_cokerRepresentation_of_isFredholm`: both apply to equivariant
  Fredholm operators between normed spaces.
* `ContIntertwiningMap.isometry_cokerEquivOrthogonalRange` and
  `ContIntertwiningMap.isometry_cokerEquivKerAdjoint`: the identifications of the cokernel preserve
  norms.

## References

* M. F. Atiyah and I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  484–530, for the equivariant index `[ker T] - [coker T]` of an operator commuting with a compact
  group action, as a virtual representation.
-/

public section

open ContRepresentation

namespace ContIntertwiningMap

/-! ### Strong continuity of the kernel and cokernel representations -/

section Representations

variable {R G V W : Type*} [Ring R] [Monoid G] [AddCommGroup V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [Module R V] [AddCommGroup W] [TopologicalSpace W]
  [IsTopologicalAddGroup W] [Module R W] [TopologicalSpace G]
  {π : ContRepresentation R G V} {ρ : ContRepresentation R G W} (T : π →ⁱL ρ)

/-- The kernel representation of an intertwining map out of a strongly continuous representation
is strongly continuous. -/
theorem continuous_kerRepresentation_apply (hπ : ∀ v, Continuous fun g ↦ π g v)
    (v : T.toContinuousLinearMap.ker) : Continuous fun g ↦ T.kerRepresentation g v :=
  T.kerRepresentation_eq_subrepresentation ▸ continuous_subrepresentation_apply hπ v

/-- The cokernel representation of an intertwining map into a strongly continuous representation
is strongly continuous. -/
theorem continuous_cokerRepresentation_apply (hρ : ∀ w, Continuous fun g ↦ ρ g w)
    (x : W ⧸ T.toContinuousLinearMap.range) : Continuous fun g ↦ T.cokerRepresentation g x :=
  T.cokerRepresentation_eq_quotient ▸ continuous_quotient_apply hρ x

end Representations

/-! ### Continuity of the kernel and cokernel representations -/

section Kernel

variable {𝕜 G E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [Monoid G]
  [TopologicalSpace G] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] {π : ContRepresentation 𝕜 G E} {ρ : ContRepresentation 𝕜 G F} (T : π →ⁱL ρ)

/-- **The kernel carries a continuous representation.** If an intertwining map out of a strongly
continuous representation has finite-dimensional kernel, then the kernel representation is
continuous for the operator norm. -/
theorem continuous_kerRepresentation (hπ : ∀ v, Continuous fun g ↦ π g v)
    [FiniteDimensional 𝕜 T.toContinuousLinearMap.ker] : Continuous T.kerRepresentation :=
  continuous_clm_apply.mpr (T.continuous_kerRepresentation_apply hπ)

/-- **The kernel of an equivariant Fredholm operator is a continuous representation.** For a
Fredholm operator intertwining strongly continuous representations, the action on its
finite-dimensional kernel is continuous for the operator norm. -/
theorem continuous_kerRepresentation_of_isFredholm (hT : T.toContinuousLinearMap.IsFredholm)
    (hπ : ∀ v, Continuous fun g ↦ π g v) : Continuous T.kerRepresentation :=
  have := hT.finite_ker
  T.continuous_kerRepresentation hπ

/-- **The cokernel carries a continuous representation.** If an intertwining map into a strongly
continuous representation has closed range and finite-dimensional cokernel, then the cokernel
representation is continuous for the operator norm. -/
theorem continuous_cokerRepresentation (hρ : ∀ w, Continuous fun g ↦ ρ g w)
    [IsClosed (T.toContinuousLinearMap.range : Set F)]
    [FiniteDimensional 𝕜 (F ⧸ T.toContinuousLinearMap.range)] :
    Continuous T.cokerRepresentation :=
  continuous_clm_apply.mpr (T.continuous_cokerRepresentation_apply hρ)

/-- **The cokernel of an equivariant Fredholm operator is a continuous representation.** For a
Fredholm operator intertwining strongly continuous representations, the action on its
finite-dimensional cokernel is continuous for the operator norm. -/
theorem continuous_cokerRepresentation_of_isFredholm (hT : T.toContinuousLinearMap.IsFredholm)
    (hρ : ∀ w, Continuous fun g ↦ ρ g w) : Continuous T.cokerRepresentation :=
  have := hT.isClosed_range
  have := hT.finite_coker
  T.continuous_cokerRepresentation hρ

end Kernel

section KernelUnitary

variable {𝕜 G E F : Type*} [RCLike 𝕜] [Monoid G] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {π : ContRepresentation 𝕜 G E} {ρ : ContRepresentation 𝕜 G F} (T : π →ⁱL ρ)

/-- The kernel representation of an intertwining map out of a unitary representation is
unitary. -/
theorem isUnitary_kerRepresentation (hπ : π.IsUnitary) : T.kerRepresentation.IsUnitary :=
  T.kerRepresentation_eq_subrepresentation ▸ hπ.subrepresentation _

end KernelUnitary

/-! ### The cokernel as the orthogonal complement of the range -/

section Cokernel

variable {𝕜 G E F : Type*} [RCLike 𝕜] [Group G] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  {π : ContRepresentation 𝕜 G E} {ρ : ContRepresentation 𝕜 G F} (T : π →ⁱL ρ)

/-- For a unitary target representation `ρ`, the action of `G` on the orthogonal complement of the
range of an intertwining map `T : π →ⁱL ρ`, which is invariant because the range is. -/
def orthogonalRangeRepresentation (hρ : ρ.IsUnitary) :
    ContRepresentation 𝕜 G T.toContinuousLinearMap.rangeᗮ :=
  ρ.subrepresentation _ fun g _ hv ↦
    hρ.apply_mem_orthogonal (fun g _ hw ↦ T.toIntertwiningMap.range.apply_mem_toSubmodule g hw) g hv

/-- The representation on the orthogonal complement of the range acts as `ρ` on the underlying
vectors. -/
@[simp]
theorem coe_orthogonalRangeRepresentation_apply (hρ : ρ.IsUnitary) (g : G)
    (v : T.toContinuousLinearMap.rangeᗮ) :
    ((T.orthogonalRangeRepresentation hρ g v : T.toContinuousLinearMap.rangeᗮ) : F) = ρ g v :=
  coe_subrepresentation_apply g v

/-- The representation on the orthogonal complement of the range is unitary. -/
theorem isUnitary_orthogonalRangeRepresentation (hρ : ρ.IsUnitary) :
    (T.orthogonalRangeRepresentation hρ).IsUnitary :=
  hρ.subrepresentation _

variable [TopologicalSpace G] in
/-- A finite-dimensional orthogonal complement of the range of an intertwining map into a strongly
continuous unitary representation carries a continuous representation. -/
theorem continuous_orthogonalRangeRepresentation (hρ : ρ.IsUnitary)
    (hρc : ∀ w, Continuous fun g ↦ ρ g w) [FiniteDimensional 𝕜 T.toContinuousLinearMap.rangeᗮ] :
    Continuous (T.orthogonalRangeRepresentation hρ) :=
  continuous_clm_apply.mpr (continuous_subrepresentation_apply hρc)

section OrthogonalProjection

variable [T.toContinuousLinearMap.range.HasOrthogonalProjection]

/-- **The cokernel is the orthogonal complement of the range, equivariantly.** For a unitary target
representation and a range admitting an orthogonal projection, Mathlib's isometric identification
`Submodule.quotientEquivOrthogonal` of `F ⧸ range T` with `(range T)ᗮ` intertwines the cokernel
representation with the representation on the orthogonal complement. Its inverse sends a vector of
the orthogonal complement to its class (`cokerEquivOrthogonalRange_symm_apply`). -/
noncomputable def cokerEquivOrthogonalRange (hρ : ρ.IsUnitary) :
    T.cokerRepresentation.Equiv (T.orthogonalRangeRepresentation hρ) :=
  (ContRepresentation.Equiv.mk
    T.toContinuousLinearMap.range.quotientEquivOrthogonal.symm.toContinuousLinearEquiv
    fun g ↦ by
      ext ⟨v, hv⟩
      simp [Submodule.quotientEquivOrthogonal_symm_eq_mk]).symm

/-- The identification of the orthogonal complement of the range with the cokernel sends a vector
to its class. -/
@[simp]
theorem cokerEquivOrthogonalRange_symm_apply (hρ : ρ.IsUnitary)
    (v : T.toContinuousLinearMap.rangeᗮ) :
    (T.cokerEquivOrthogonalRange hρ).symm v = Submodule.Quotient.mk (v : F) := by
  simp [cokerEquivOrthogonalRange]

/-- The identification of the cokernel with the orthogonal complement of the range sends the class
of `w` to the orthogonal projection of `w` onto that complement. -/
@[simp]
theorem cokerEquivOrthogonalRange_apply_mk (hρ : ρ.IsUnitary) (w : F) :
    T.cokerEquivOrthogonalRange hρ (Submodule.Quotient.mk w) =
      T.toContinuousLinearMap.rangeᗮ.orthogonalProjectionOnto w := by
  simp [cokerEquivOrthogonalRange, Submodule.orthogonalProjectionOnto_apply_eq_projectionOnto]

/-- The identification of the cokernel with the orthogonal complement of the range preserves
norms, since it is Mathlib's isometry `Submodule.quotientEquivOrthogonal`. -/
@[simp]
theorem norm_cokerEquivOrthogonalRange_apply (hρ : ρ.IsUnitary)
    (x : F ⧸ T.toContinuousLinearMap.range) :
    ‖(T.cokerEquivOrthogonalRange hρ x : F)‖ = ‖x‖ :=
  T.toContinuousLinearMap.range.quotientEquivOrthogonal.norm_map x

/-- The identification of the cokernel with the orthogonal complement of the range is an
isometry. -/
theorem isometry_cokerEquivOrthogonalRange (hρ : ρ.IsUnitary) :
    Isometry (T.cokerEquivOrthogonalRange hρ) :=
  AddMonoidHomClass.isometry_of_norm _ (T.norm_cokerEquivOrthogonalRange_apply hρ)

end OrthogonalProjection

end Cokernel

/-! ### The cokernel as the kernel of the adjoint -/

section Adjoint

variable {𝕜 G E F : Type*} [RCLike 𝕜] [Group G] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  {π : ContRepresentation 𝕜 G E} {ρ : ContRepresentation 𝕜 G F} (T : π →ⁱL ρ)

variable [T.toContinuousLinearMap.range.HasOrthogonalProjection]

/-- **The cokernel is the kernel of the adjoint, equivariantly.** For unitary representations on
Hilbert spaces and a range admitting an orthogonal projection, the cokernel representation of `T`
is equivalent to the kernel representation of the adjoint intertwining map
`ContIntertwiningMap.adjoint`, through the orthogonal complement of the range, which is the kernel
of the adjoint (`ContinuousLinearMap.orthogonal_range`). This is the equivariant form of
`ContinuousLinearMap.cokerEquivKerAdjoint`. -/
noncomputable def cokerEquivKerAdjoint (hπ : π.IsUnitary) (hρ : ρ.IsUnitary) :
    T.cokerRepresentation.Equiv (T.adjoint hπ hρ).kerRepresentation :=
  (T.cokerEquivOrthogonalRange hρ).trans <| ContRepresentation.Equiv.mk
    (LinearIsometryEquiv.ofEq _ _ <| by
      rw [toContinuousLinearMap_adjoint]
      exact T.toContinuousLinearMap.orthogonal_range).toContinuousLinearEquiv
    fun g ↦ by
      ext v
      simp

/-- The equivariant identification of the cokernel with the kernel of the adjoint sends the class
of `w` to the orthogonal projection of `w` onto the orthogonal complement of the range. -/
@[simp]
theorem coe_cokerEquivKerAdjoint_apply_mk (hπ : π.IsUnitary) (hρ : ρ.IsUnitary) (w : F) :
    (T.cokerEquivKerAdjoint hπ hρ (Submodule.Quotient.mk w) : F) =
      T.toContinuousLinearMap.rangeᗮ.orthogonalProjectionOnto w := by
  simp [cokerEquivKerAdjoint]

/-- The inverse of the equivariant identification of the cokernel with the kernel of the adjoint
sends a kernel vector to its class. -/
@[simp]
theorem cokerEquivKerAdjoint_symm_apply (hπ : π.IsUnitary) (hρ : ρ.IsUnitary)
    (v : (T.adjoint hπ hρ).toContinuousLinearMap.ker) :
    (T.cokerEquivKerAdjoint hπ hρ).symm v = Submodule.Quotient.mk (v : F) := by
  have hv : (v : F) ∈ T.toContinuousLinearMap.rangeᗮ := by
    rw [T.toContinuousLinearMap.orthogonal_range, ← toContinuousLinearMap_adjoint T hπ hρ]
    exact v.2
  apply EquivLike.injective (T.cokerEquivKerAdjoint hπ hρ)
  ext
  rw [ContRepresentation.Equiv.apply_symm_apply, coe_cokerEquivKerAdjoint_apply_mk,
    ← Submodule.starProjection_apply, Submodule.starProjection_eq_self_iff.mpr hv]

/-- The equivariant identification of the cokernel with the kernel of the adjoint preserves
norms. -/
@[simp]
theorem norm_cokerEquivKerAdjoint_apply (hπ : π.IsUnitary) (hρ : ρ.IsUnitary)
    (x : F ⧸ T.toContinuousLinearMap.range) :
    ‖(T.cokerEquivKerAdjoint hπ hρ x : F)‖ = ‖x‖ := by
  have h : (T.cokerEquivKerAdjoint hπ hρ x : F) = T.cokerEquivOrthogonalRange hρ x := by
    induction x using Submodule.Quotient.induction_on with
    | H w => rw [coe_cokerEquivKerAdjoint_apply_mk, cokerEquivOrthogonalRange_apply_mk]
  rw [h, norm_cokerEquivOrthogonalRange_apply]

/-- The equivariant identification of the cokernel with the kernel of the adjoint is an
isometry. -/
theorem isometry_cokerEquivKerAdjoint (hπ : π.IsUnitary) (hρ : ρ.IsUnitary) :
    Isometry (T.cokerEquivKerAdjoint hπ hρ) :=
  AddMonoidHomClass.isometry_of_norm _ (T.norm_cokerEquivKerAdjoint_apply hπ hρ)

end Adjoint

end ContIntertwiningMap
