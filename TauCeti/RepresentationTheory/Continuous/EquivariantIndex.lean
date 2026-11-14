/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Adjoint
public import TauCeti.RepresentationTheory.Continuous.KernelCokernel
public import TauCeti.RepresentationTheory.RepresentationRing.Continuous

/-!
# The equivariant index of an equivariant Fredholm operator

Let a topological monoid `G` act on normed spaces `E` and `F` by strongly continuous
representations `π` and `ρ`, and let `T : π →ⁱL ρ` be an intertwining map whose underlying operator
is Fredholm. Its kernel and cokernel are finite-dimensional and carry genuine continuous
representations (`ContIntertwiningMap.continuous_kerRepresentation_of_isFredholm` and
`ContIntertwiningMap.continuous_cokerRepresentation_of_isFredholm`). The **equivariant index** of
`T` is the virtual representation

`ind_G T = [ker T] - [coker T]`

in the representation ring `TauCeti.contRepRing 𝕜 G` of continuous finite-dimensional
representations. For a compact group acting on bundles over a compact manifold and an elliptic
operator commuting with the action, this is the analytic index of Atiyah and Singer with values in
`R(G)`.

The equivariant index refines the Fredholm index: its character at `g` is the trace of `g` on the
kernel minus its trace on the cokernel, so at `g = 1` it is `dim ker T - dim coker T`. It vanishes
on invertible operators and does not change under composition with equivalences of
representations on either side. For unitary representations on Hilbert spaces, the cokernel is the
kernel of the adjoint, so `ind_G T = [ker T] - [ker T†]` and `ind_G T† = - ind_G T`.

## Main definitions

* `ContIntertwiningMap.equivariantIndex`: the virtual representation `[ker T] - [coker T]` of an
  equivariant Fredholm operator.

## Main statements

* `ContIntertwiningMap.equivariantIndex_def`: the defining formula.
* `ContIntertwiningMap.repRingCharacter_equivariantIndex`: the character of the equivariant index
  is the difference of the characters of the kernel and the cokernel.
* `ContIntertwiningMap.repRingCharacter_equivariantIndex_one`: evaluated at the identity, the
  character is the Fredholm index.
* `ContIntertwiningMap.equivariantIndex_eq_zero_of_bijective`: bijective intertwining maps have
  equivariant index zero.
* `ContIntertwiningMap.equivariantIndex_comp_equiv` and
  `ContIntertwiningMap.equivariantIndex_equiv_comp`: composing with an equivalence of
  representations does not change the equivariant index.
* `ContIntertwiningMap.equivariantIndex_eq_sub_ker_adjoint`: for unitary representations on Hilbert
  spaces, `ind_G T = [ker T] - [ker T†]`.
* `ContIntertwiningMap.equivariantIndex_adjoint`: taking the adjoint negates the equivariant index.

## References

* M. F. Atiyah and I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  484–530, §6, for the equivariant index `[ker T] - [coker T]` with values in the representation
  ring `R(G)`.
-/

public section

open CategoryTheory ContRepresentation TauCeti

namespace ContIntertwiningMap

section Basic

variable {𝕜 G E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [Monoid G]
  [TopologicalSpace G] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] {π : ContRepresentation 𝕜 G E} {ρ : ContRepresentation 𝕜 G F}

/-- **The equivariant index** of an intertwining map `T : π →ⁱL ρ` between strongly continuous
representations whose underlying operator is Fredholm: the virtual representation
`[ker T] - [coker T]` in the representation ring of continuous finite-dimensional representations.
The kernel and cokernel representations are continuous for the operator norm by
`ContIntertwiningMap.continuous_kerRepresentation_of_isFredholm` and
`ContIntertwiningMap.continuous_cokerRepresentation_of_isFredholm`. -/
noncomputable def equivariantIndex (T : π →ⁱL ρ) (hT : T.toContinuousLinearMap.IsFredholm)
    (hπ : ∀ v, Continuous fun g ↦ π g v) (hρ : ∀ w, Continuous fun g ↦ ρ g w) :
    contRepRing 𝕜 G :=
  have := hT.finite_ker
  have := hT.isClosed_range
  have := hT.finite_coker
  SplitK0.of (ContFDRep.ofContRepresentation T.kerRepresentation
      (T.continuous_kerRepresentation_of_isFredholm hT hπ)) -
    SplitK0.of (ContFDRep.ofContRepresentation T.cokerRepresentation
      (T.continuous_cokerRepresentation_of_isFredholm hT hρ))

variable (T : π →ⁱL ρ) (hT : T.toContinuousLinearMap.IsFredholm)
  (hπ : ∀ v, Continuous fun g ↦ π g v) (hρ : ∀ w, Continuous fun g ↦ ρ g w)

/-- The equivariant index is the class of the kernel representation minus the class of the
cokernel representation. The instance arguments, which hold for every Fredholm operator, are the
ones needed to state the formula. -/
theorem equivariantIndex_def [FiniteDimensional 𝕜 T.toContinuousLinearMap.ker]
    [IsClosed (T.toContinuousLinearMap.range : Set F)]
    [FiniteDimensional 𝕜 (F ⧸ T.toContinuousLinearMap.range)] :
    T.equivariantIndex hT hπ hρ =
      SplitK0.of (ContFDRep.ofContRepresentation T.kerRepresentation
          (T.continuous_kerRepresentation hπ)) -
        SplitK0.of (ContFDRep.ofContRepresentation T.cokerRepresentation
          (T.continuous_cokerRepresentation hρ)) :=
  (rfl)

/-- **The character of the equivariant index** is the character of the kernel representation minus
the character of the cokernel representation: at `g`, the trace of `g` on `ker T` minus its trace
on `coker T`. -/
@[simp]
theorem repRingCharacter_equivariantIndex (g : G) :
    repRingCharacter 𝕜 G (contRepRingToRepRing 𝕜 G (T.equivariantIndex hT hπ hρ)) g =
      T.kerRepresentation.toRepresentation.character g -
        T.cokerRepresentation.toRepresentation.character g := by
  have := hT.finite_ker
  have := hT.isClosed_range
  have := hT.finite_coker
  simp [T.equivariantIndex_def]

/-- **The equivariant index refines the Fredholm index**: the character of the equivariant index at
the identity is `dim ker T - dim coker T`. -/
theorem repRingCharacter_equivariantIndex_one :
    repRingCharacter 𝕜 G (contRepRingToRepRing 𝕜 G (T.equivariantIndex hT hπ hρ)) 1 =
      (T.toContinuousLinearMap.index : 𝕜) := by
  have := hT.finite_ker
  have := hT.finite_coker
  simp [repRingCharacter_equivariantIndex, ContinuousLinearMap.index_eq_finrank_sub]

/-- **A bijective intertwining map has equivariant index zero**: its kernel and cokernel are both
zero. -/
theorem equivariantIndex_eq_zero_of_bijective (h : Function.Bijective T) :
    T.equivariantIndex hT hπ hρ = 0 := by
  have := hT.finite_ker
  have := hT.isClosed_range
  have := hT.finite_coker
  have hker : Subsingleton T.toContinuousLinearMap.ker := by
    rw [Submodule.subsingleton_iff_eq_bot, LinearMap.ker_eq_bot]
    exact h.injective
  have hcoker : Subsingleton (F ⧸ T.toContinuousLinearMap.range) := by
    rw [Submodule.Quotient.subsingleton_iff, LinearMap.range_eq_top]
    exact h.surjective
  rw [equivariantIndex_def,
    SplitK0.of_eq_zero_of_isZero (ContFDRep.isZero_ofContRepresentation _ _),
    SplitK0.of_eq_zero_of_isZero (ContFDRep.isZero_ofContRepresentation _ _), sub_zero]

/-- The identity intertwining map has equivariant index zero. -/
@[simp]
theorem equivariantIndex_id
    (hT : (ContIntertwiningMap.id : π →ⁱL π).toContinuousLinearMap.IsFredholm) :
    (ContIntertwiningMap.id : π →ⁱL π).equivariantIndex hT hπ hπ = 0 :=
  equivariantIndex_eq_zero_of_bijective _ _ _ _ Function.bijective_id

end Basic

section Composition

variable {𝕜 G E F F' : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [Monoid G]
  [TopologicalSpace G] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {π : ContRepresentation 𝕜 G E} {ρ : ContRepresentation 𝕜 G F} {σ : ContRepresentation 𝕜 G F'}

/-- **Composing on the right with an equivalence does not change the equivariant index.** For an
equivalence `e : π ≃ ρ` and an equivariant Fredholm `T : ρ →ⁱL σ`, the composite `T ∘ e` has the
same equivariant index as `T`: `e` maps the kernel of `T ∘ e` equivariantly onto the kernel of `T`,
and both operators have the same range. -/
theorem equivariantIndex_comp_equiv (T : ρ →ⁱL σ) (e : π.Equiv ρ)
    (hT : T.toContinuousLinearMap.IsFredholm)
    (hπ : ∀ v, Continuous fun g ↦ π g v) (hρ : ∀ v, Continuous fun g ↦ ρ g v)
    (hσ : ∀ w, Continuous fun g ↦ σ g w) :
    (T.comp e.toContIntertwiningMap).equivariantIndex
        (hT.comp_equiv e.toContinuousLinearEquiv) hπ hσ =
      T.equivariantIndex hT hρ hσ := by
  have := hT.finite_ker
  have := hT.isClosed_range
  have := hT.finite_coker
  have hTe : (T.comp e.toContIntertwiningMap).toContinuousLinearMap.IsFredholm :=
    hT.comp_equiv e.toContinuousLinearEquiv
  change (T.comp e.toContIntertwiningMap).equivariantIndex hTe hπ hσ = _
  have := hTe.finite_ker
  have := hTe.isClosed_range
  have := hTe.finite_coker
  have hker : (T.comp e.toContIntertwiningMap).toContinuousLinearMap.ker.map
      (e.toLinearEquiv : E →ₗ[𝕜] F) = T.toContinuousLinearMap.ker :=
    (congrArg _ (LinearMap.ker_comp _ _)).trans
      (Submodule.map_comap_eq_of_surjective e.surjective _)
  have hrange : (T.comp e.toContIntertwiningMap).toContinuousLinearMap.range =
      T.toContinuousLinearMap.range :=
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr e.surjective)
  rw [equivariantIndex_def, equivariantIndex_def]
  congr 1
  · refine SplitK0.of_congr (ContFDRep.ofContRepresentationIso
      (e.toLinearEquiv.ofSubmodules _ _ hker) (fun g v ↦ ?_) _ _)
    ext
    simp only [LinearEquiv.ofSubmodules_apply, coe_kerRepresentation_apply]
    exact e.toContIntertwiningMap.isIntertwining g v
  · refine SplitK0.of_congr (ContFDRep.ofContRepresentationIso
      (Submodule.quotEquivOfEq _ _ hrange) (fun g x ↦ ?_) _ _)
    induction x using Submodule.Quotient.induction_on with
    | H w =>
      rw [cokerRepresentation_apply_mk, Submodule.quotEquivOfEq_mk, Submodule.quotEquivOfEq_mk,
        cokerRepresentation_apply_mk]

/-- **Composing on the left with an equivalence does not change the equivariant index.** For an
equivariant Fredholm `T : π →ⁱL ρ` and an equivalence `e : ρ ≃ σ`, the composite `e ∘ T` has the
same equivariant index as `T`: both operators have the same kernel, and `e` maps the cokernel of `T`
equivariantly onto the cokernel of `e ∘ T`. -/
theorem equivariantIndex_equiv_comp (T : π →ⁱL ρ) (e : ρ.Equiv σ)
    (hT : T.toContinuousLinearMap.IsFredholm)
    (hπ : ∀ v, Continuous fun g ↦ π g v) (hρ : ∀ v, Continuous fun g ↦ ρ g v)
    (hσ : ∀ w, Continuous fun g ↦ σ g w) :
    (e.toContIntertwiningMap.comp T).equivariantIndex
        (hT.equiv_comp e.toContinuousLinearEquiv) hπ hσ =
      T.equivariantIndex hT hπ hρ := by
  have := hT.finite_ker
  have := hT.isClosed_range
  have := hT.finite_coker
  have heT : (e.toContIntertwiningMap.comp T).toContinuousLinearMap.IsFredholm :=
    hT.equiv_comp e.toContinuousLinearEquiv
  change (e.toContIntertwiningMap.comp T).equivariantIndex heT hπ hσ = _
  have := heT.finite_ker
  have := heT.isClosed_range
  have := heT.finite_coker
  have hker : (e.toContIntertwiningMap.comp T).toContinuousLinearMap.ker =
      T.toContinuousLinearMap.ker :=
    LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.mpr e.injective)
  have hrange : T.toContinuousLinearMap.range.map (e.toLinearEquiv : F →ₗ[𝕜] F') =
      (e.toContIntertwiningMap.comp T).toContinuousLinearMap.range :=
    (LinearMap.range_comp _ _).symm
  rw [equivariantIndex_def, equivariantIndex_def]
  congr 1
  · refine SplitK0.of_congr (ContFDRep.ofContRepresentationIso
      (LinearEquiv.ofEq _ _ hker) (fun g v ↦ ?_) _ _)
    ext
    simp only [LinearEquiv.coe_ofEq_apply, coe_kerRepresentation_apply]
  · refine SplitK0.of_congr (ContFDRep.ofContRepresentationIso
      (Submodule.Quotient.equiv _ _ e.toLinearEquiv hrange).symm (fun g x ↦ ?_) _ _)
    induction x using Submodule.Quotient.induction_on with
    | H w =>
      simp only [cokerRepresentation_apply_mk, Submodule.Quotient.equiv_symm,
        Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]
      congr 1
      exact e.toLinearEquiv.symm_apply_eq.mpr
        ((e.toContIntertwiningMap.isIntertwining g _).trans
          (congrArg (σ g) (e.apply_symm_apply w))).symm

end Composition

section Adjoint

variable {𝕜 G E F : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [CompleteSpace F] {π : ContRepresentation 𝕜 G E} {ρ : ContRepresentation 𝕜 G F}
  (T : π →ⁱL ρ) (hT : T.toContinuousLinearMap.IsFredholm)
  (hπ : ∀ v, Continuous fun g ↦ π g v) (hρ : ∀ w, Continuous fun g ↦ ρ g w)
  (hπu : π.IsUnitary) (hρu : ρ.IsUnitary)

/-- **The cokernel as the kernel of the adjoint.** For unitary representations on Hilbert spaces,
the equivariant index of `T` is the class of its kernel minus the class of the kernel of its
adjoint, by the equivariant identification `ContIntertwiningMap.cokerEquivKerAdjoint`. The
instance arguments, which hold for every Fredholm operator, are the ones needed to state the
formula. -/
theorem equivariantIndex_eq_sub_ker_adjoint [FiniteDimensional 𝕜 T.toContinuousLinearMap.ker]
    [FiniteDimensional 𝕜 (T.adjoint hπu hρu).toContinuousLinearMap.ker] :
    T.equivariantIndex hT hπ hρ =
      SplitK0.of (ContFDRep.ofContRepresentation T.kerRepresentation
          (T.continuous_kerRepresentation hπ)) -
        SplitK0.of (ContFDRep.ofContRepresentation (T.adjoint hπu hρu).kerRepresentation
          ((T.adjoint hπu hρu).continuous_kerRepresentation hρ)) := by
  have := hT.isClosed_range
  have := hT.finite_coker
  have : CompleteSpace T.toContinuousLinearMap.range := hT.isClosed_range.completeSpace_coe
  let e := T.cokerEquivKerAdjoint hπu hρu
  rw [equivariantIndex_def]
  congr 1
  exact SplitK0.of_congr (ContFDRep.ofContRepresentationIso
    e.toContinuousLinearEquiv.toLinearEquiv e.toContIntertwiningMap.isIntertwining _ _)

/-- **Taking the adjoint negates the equivariant index**: `ind_G T† = - ind_G T` for an
equivariant Fredholm operator between unitary representations on Hilbert spaces. This refines
`ContinuousLinearMap.index_adjoint`. -/
theorem equivariantIndex_adjoint :
    (T.adjoint hπu hρu).equivariantIndex
        (T.toContinuousLinearMap_adjoint hπu hρu ▸ hT.adjoint) hρ hπ =
      -T.equivariantIndex hT hπ hρ := by
  have hT' : (T.adjoint hπu hρu).toContinuousLinearMap.IsFredholm :=
    T.toContinuousLinearMap_adjoint hπu hρu ▸ hT.adjoint
  have := hT.finite_ker
  have := hT'.finite_ker
  have : FiniteDimensional 𝕜
      ((T.adjoint hπu hρu).adjoint hρu hπu).toContinuousLinearMap.ker := by
    rwa [adjoint_adjoint]
  rw [T.equivariantIndex_eq_sub_ker_adjoint hT hπ hρ hπu hρu,
    (T.adjoint hπu hρu).equivariantIndex_eq_sub_ker_adjoint hT' hρ hπ hρu hπu, neg_sub]
  congr 1
  refine SplitK0.of_congr (ContFDRep.ofContRepresentationIso
    (LinearEquiv.ofEq _ _ (by rw [adjoint_adjoint])) (fun g v ↦ ?_) _ _)
  ext
  simp only [LinearEquiv.coe_ofEq_apply, coe_kerRepresentation_apply]

end Adjoint

end ContIntertwiningMap
