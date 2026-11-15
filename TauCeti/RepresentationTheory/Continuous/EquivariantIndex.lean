/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.KernelCokernel
public import TauCeti.RepresentationTheory.Continuous.Multiplicity
public import TauCeti.RepresentationTheory.RepresentationRing.Continuous
import TauCeti.Analysis.Fredholm.Adjoint

/-!
# The equivariant index

Let a topological monoid `G` act on normed spaces `E` and `F` by strongly continuous
representations `π` and `ρ`, as translation actions on spaces of sections do, and let
`T : E → F` be a Fredholm operator intertwining them. Its kernel and cokernel are
finite-dimensional, and `G` acts on them by representations that are continuous for the operator
norm (`ContIntertwiningMap.continuous_kerRepresentation_of_isFredholm`,
`ContIntertwiningMap.continuous_cokerRepresentation_of_isFredholm`). The **equivariant index** of
`T` is the virtual representation

`ind_G T = [ker T] - [coker T]`

in the representation ring `R(G) = TauCeti.contRepRing 𝕜 G` of continuous finite-dimensional
representations (`ContIntertwiningMap.equivariantIndex`). It refines the Fredholm index, which is
its virtual dimension: the character of `ind_G T` at `g` is the trace of `g` on the kernel minus
its trace on the cokernel (`ContIntertwiningMap.repRingCharacter_equivariantIndex`), and at the
identity it is `index T` (`ContIntertwiningMap.repRingCharacter_equivariantIndex_one`).

For unitary representations on Hilbert spaces the cokernel is equivalent to the kernel of the
adjoint, so `ind_G T = [ker T] - [ker T†]`, and `ind_G T† = -ind_G T`
(`ContIntertwiningMap.equivariantIndex_adjoint`). The multiplicity of a finite-dimensional
continuous representation `σ` in `ind_G T`, read through `TauCeti.contRepRingMultiplicity`, is
`dim Hom_G(σ, ker T) - dim Hom_G(σ, coker T)`
(`ContIntertwiningMap.contRepRingMultiplicity_equivariantIndex`). That difference is the index
of the action of `T` on the multiplicity spaces of `σ`, so it is constant along norm-continuous
families of equivariant Fredholm operators: the multiplicities of the equivariant index are
homotopy invariant (`ContinuousOn.contRepRingMultiplicity_equivariantIndex_eq`). For a compact
group over `ℂ`, complete reducibility and Schur's lemma make a virtual representation determined
by these multiplicities over the irreducible `σ`, and through that comparison the invariance of
the multiplicities becomes the homotopy invariance of the class `ind_G T` itself.

## Main definitions

* `ContIntertwiningMap.equivariantIndex`: the equivariant index `[ker T] - [coker T]` of an
  equivariant Fredholm operator.

## Main statements

* `ContIntertwiningMap.repRingCharacter_equivariantIndex_one`: the virtual dimension of the
  equivariant index is the Fredholm index.
* `ContIntertwiningMap.equivariantIndex_eq_zero_of_bijective`: an invertible operator has
  equivariant index zero.
* `ContIntertwiningMap.equivariantIndex_eq_sub_kerRepresentation_adjoint` and
  `ContIntertwiningMap.equivariantIndex_adjoint`: for unitary representations the index is
  `[ker T] - [ker T†]`, and adjunction changes its sign.
* `ContinuousOn.contRepRingMultiplicity_equivariantIndex_eq`: homotopy invariance of the
  multiplicities of the equivariant index.

## References

* M. F. Atiyah and I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  484–530, §§4 and 6, for the equivariant index of an operator commuting with a compact group
  action as an element of the representation ring.
-/

public section

open CategoryTheory TauCeti ContRepresentation

namespace ContIntertwiningMap

section Basic

variable {𝕜 G E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [Monoid G]
  [TopologicalSpace G] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] {π : ContRepresentation 𝕜 G E} {ρ : ContRepresentation 𝕜 G F} (T : π →ⁱL ρ)

/-- **The equivariant index** of a Fredholm operator `T` intertwining strongly continuous
representations: the virtual representation `[ker T] - [coker T]` in the representation ring of
continuous finite-dimensional representations. -/
noncomputable def equivariantIndex (hT : T.toContinuousLinearMap.IsFredholm)
    (hπ : ∀ v, Continuous fun g ↦ π g v) (hρ : ∀ w, Continuous fun g ↦ ρ g w) :
    contRepRing 𝕜 G :=
  have := hT.finite_ker
  have := hT.isClosed_range
  have := hT.finite_coker
  SplitK0.of (ContFDRep.ofContRepresentation T.kerRepresentation
      (T.continuous_kerRepresentation_of_isFredholm hT hπ)) -
    SplitK0.of (ContFDRep.ofContRepresentation T.cokerRepresentation
      (T.continuous_cokerRepresentation_of_isFredholm hT hρ))

/-- The equivariant index is the class of the kernel minus the class of the cokernel, for any
choice of the finiteness and continuity facts that define these classes. -/
theorem equivariantIndex_eq (hT : T.toContinuousLinearMap.IsFredholm)
    (hπ : ∀ v, Continuous fun g ↦ π g v) (hρ : ∀ w, Continuous fun g ↦ ρ g w)
    [FiniteDimensional 𝕜 T.toContinuousLinearMap.ker]
    [IsClosed (T.toContinuousLinearMap.range : Set F)]
    [FiniteDimensional 𝕜 (F ⧸ T.toContinuousLinearMap.range)]
    (hker : Continuous T.kerRepresentation) (hcoker : Continuous T.cokerRepresentation) :
    T.equivariantIndex hT hπ hρ =
      SplitK0.of (ContFDRep.ofContRepresentation T.kerRepresentation hker) -
        SplitK0.of (ContFDRep.ofContRepresentation T.cokerRepresentation hcoker) :=
  (rfl)

/-- The character of the equivariant index at `g` is the trace of `g` on the kernel minus its
trace on the cokernel. -/
theorem repRingCharacter_equivariantIndex (hT : T.toContinuousLinearMap.IsFredholm)
    (hπ : ∀ v, Continuous fun g ↦ π g v) (hρ : ∀ w, Continuous fun g ↦ ρ g w) :
    repRingCharacter 𝕜 G (contRepRingToRepRing 𝕜 G (T.equivariantIndex hT hπ hρ)) =
      T.kerRepresentation.toRepresentation.character -
        T.cokerRepresentation.toRepresentation.character := by
  have := hT.finite_ker
  have := hT.isClosed_range
  have := hT.finite_coker
  rw [T.equivariantIndex_eq hT hπ hρ (T.continuous_kerRepresentation_of_isFredholm hT hπ)
    (T.continuous_cokerRepresentation_of_isFredholm hT hρ), map_sub, map_sub,
    repRingCharacter_contRepRingToRepRing_of_ofContRepresentation,
    repRingCharacter_contRepRingToRepRing_of_ofContRepresentation]

/-- **The equivariant index refines the Fredholm index**: its character at the identity, the
virtual dimension, is the index of `T`. -/
theorem repRingCharacter_equivariantIndex_one (hT : T.toContinuousLinearMap.IsFredholm)
    (hπ : ∀ v, Continuous fun g ↦ π g v) (hρ : ∀ w, Continuous fun g ↦ ρ g w) :
    repRingCharacter 𝕜 G (contRepRingToRepRing 𝕜 G (T.equivariantIndex hT hπ hρ)) 1 =
      (T.toContinuousLinearMap.index : 𝕜) := by
  have := hT.finite_ker
  have := hT.finite_coker
  rw [repRingCharacter_equivariantIndex, Pi.sub_apply, Representation.char_one,
    Representation.char_one, ContinuousLinearMap.index_eq_finrank_sub]
  norm_cast

/-- The multiplicity of a finite-dimensional continuous representation `σ` in the equivariant
index is the dimension of the intertwiners from `σ` into the kernel minus that into the
cokernel. -/
theorem contRepRingMultiplicity_equivariantIndex {V : Type*} [NormedAddCommGroup V]
    [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V] (σ : ContRepresentation 𝕜 G V) (hσ : Continuous σ)
    (hT : T.toContinuousLinearMap.IsFredholm) (hπ : ∀ v, Continuous fun g ↦ π g v)
    (hρ : ∀ w, Continuous fun g ↦ ρ g w) :
    contRepRingMultiplicity (ContFDRep.ofContRepresentation σ hσ) (T.equivariantIndex hT hπ hρ) =
      Module.finrank 𝕜 (σ →ⁱL T.kerRepresentation) -
        Module.finrank 𝕜 (σ →ⁱL T.cokerRepresentation) := by
  have := hT.finite_ker
  have := hT.isClosed_range
  have := hT.finite_coker
  rw [T.equivariantIndex_eq hT hπ hρ (T.continuous_kerRepresentation_of_isFredholm hT hπ)
    (T.continuous_cokerRepresentation_of_isFredholm hT hρ), map_sub,
    contRepRingMultiplicity_of, contRepRingMultiplicity_of,
    ContFDRep.finrank_hom_ofContRepresentation, ContFDRep.finrank_hom_ofContRepresentation]

/-- An invertible intertwining map has equivariant index zero. -/
theorem equivariantIndex_eq_zero_of_bijective (hT : T.toContinuousLinearMap.IsFredholm)
    (hπ : ∀ v, Continuous fun g ↦ π g v) (hρ : ∀ w, Continuous fun g ↦ ρ g w)
    (hbij : Function.Bijective T) : T.equivariantIndex hT hπ hρ = 0 := by
  have := hT.finite_ker
  have := hT.isClosed_range
  have := hT.finite_coker
  have : Subsingleton T.toContinuousLinearMap.ker :=
    Submodule.subsingleton_iff_eq_bot.2 (LinearMap.ker_eq_bot.2 hbij.1)
  have : Subsingleton (F ⧸ T.toContinuousLinearMap.range) :=
    Submodule.Quotient.subsingleton_iff.2 (LinearMap.range_eq_top.2 hbij.2)
  rw [T.equivariantIndex_eq hT hπ hρ (T.continuous_kerRepresentation_of_isFredholm hT hπ)
    (T.continuous_cokerRepresentation_of_isFredholm hT hρ),
    SplitK0.of_eq_zero_of_isZero (ContFDRep.isZero_ofContRepresentation _),
    SplitK0.of_eq_zero_of_isZero (ContFDRep.isZero_ofContRepresentation _), sub_zero]

end Basic

section Adjoint

variable {𝕜 G E F : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [CompleteSpace F] {π : ContRepresentation 𝕜 G E} {ρ : ContRepresentation 𝕜 G F} (T : π →ⁱL ρ)

/-- For unitary representations on Hilbert spaces, the equivariant index is `[ker T] - [ker T†]`:
the cokernel is equivalent to the kernel of the adjoint. -/
theorem equivariantIndex_eq_sub_kerRepresentation_adjoint
    (hT : T.toContinuousLinearMap.IsFredholm) (hπ : ∀ v, Continuous fun g ↦ π g v)
    (hρ : ∀ w, Continuous fun g ↦ ρ g w) (hπu : π.IsUnitary) (hρu : ρ.IsUnitary)
    [FiniteDimensional 𝕜 T.toContinuousLinearMap.ker]
    [FiniteDimensional 𝕜 (T.adjoint hπu hρu).toContinuousLinearMap.ker]
    (hker : Continuous T.kerRepresentation)
    (hker' : Continuous (T.adjoint hπu hρu).kerRepresentation) :
    T.equivariantIndex hT hπ hρ =
      SplitK0.of (ContFDRep.ofContRepresentation T.kerRepresentation hker) -
        SplitK0.of
          (ContFDRep.ofContRepresentation (T.adjoint hπu hρu).kerRepresentation hker') := by
  have := hT.isClosed_range
  have := hT.finite_coker
  have : CompleteSpace T.toContinuousLinearMap.range := hT.isClosed_range.completeSpace_coe
  rw [T.equivariantIndex_eq hT hπ hρ hker (T.continuous_cokerRepresentation_of_isFredholm hT hρ),
    ContFDRep.of_ofContRepresentation_eq_of_equiv _ hker' (T.cokerEquivKerAdjoint hπu hρu)]

/-- **The equivariant index changes sign under adjunction**, for unitary representations on
Hilbert spaces. -/
theorem equivariantIndex_adjoint (hT : T.toContinuousLinearMap.IsFredholm)
    (hπ : ∀ v, Continuous fun g ↦ π g v) (hρ : ∀ w, Continuous fun g ↦ ρ g w)
    (hπu : π.IsUnitary) (hρu : ρ.IsUnitary)
    (hT' : (T.adjoint hπu hρu).toContinuousLinearMap.IsFredholm) :
    (T.adjoint hπu hρu).equivariantIndex hT' hρ hπ = -T.equivariantIndex hT hπ hρ := by
  have := hT.finite_ker
  have := hT'.finite_ker
  have hker := T.continuous_kerRepresentation_of_isFredholm hT hπ
  have hker' := (T.adjoint hπu hρu).continuous_kerRepresentation_of_isFredholm hT' hρ
  -- The double adjoint is `T` itself, so its kernel has the class of the kernel of `T`.
  have key : ∀ S : π →ⁱL ρ, S = T → ∀ [FiniteDimensional 𝕜 S.toContinuousLinearMap.ker]
      (hS : Continuous S.kerRepresentation),
      (SplitK0.of (ContFDRep.ofContRepresentation S.kerRepresentation hS) : contRepRing 𝕜 G) =
        SplitK0.of (ContFDRep.ofContRepresentation T.kerRepresentation hker) := by
    rintro S rfl _ hS
    rfl
  have : FiniteDimensional 𝕜
      ((T.adjoint hπu hρu).adjoint hρu hπu).toContinuousLinearMap.ker := by
    rw [adjoint_adjoint]
    infer_instance
  rw [(T.adjoint hπu hρu).equivariantIndex_eq_sub_kerRepresentation_adjoint hT' hρ hπ hρu hπu
      hker' (((T.adjoint hπu hρu).adjoint hρu hπu).continuous_kerRepresentation hπ),
    T.equivariantIndex_eq_sub_kerRepresentation_adjoint hT hπ hρ hπu hρu hker hker',
    key _ (adjoint_adjoint T hπu hρu), neg_sub]

/-- **Homotopy invariance of the multiplicities of the equivariant index.** Along a family of
intertwining maps between strongly continuous unitary representations on Hilbert spaces,
continuous in operator norm and Fredholm on a preconnected set `s`, the multiplicity of every
finite-dimensional continuous representation `σ` in the equivariant index is the same at every
point of `s`. -/
theorem _root_.ContinuousOn.contRepRingMultiplicity_equivariantIndex_eq {X V : Type*}
    [TopologicalSpace X] [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
    (σ : ContRepresentation 𝕜 G V) (hσ : Continuous σ) (hπ : ∀ v, Continuous fun g ↦ π g v)
    (hρ : ∀ w, Continuous fun g ↦ ρ g w) (hπu : π.IsUnitary) (hρu : ρ.IsUnitary)
    {A : X → π →ⁱL ρ} {s : Set X} (hA : ContinuousOn (fun x ↦ (A x).toContinuousLinearMap) s)
    (hFredholm : ∀ x ∈ s, (A x).toContinuousLinearMap.IsFredholm) (hs : IsPreconnected s)
    {x y : X} (hx : x ∈ s) (hy : y ∈ s) :
    contRepRingMultiplicity (ContFDRep.ofContRepresentation σ hσ)
        ((A x).equivariantIndex (hFredholm x hx) hπ hρ) =
      contRepRingMultiplicity (ContFDRep.ofContRepresentation σ hσ)
        ((A y).equivariantIndex (hFredholm y hy) hπ hρ) := by
  rw [contRepRingMultiplicity_equivariantIndex, contRepRingMultiplicity_equivariantIndex]
  exact hA.finrank_contIntertwiningMap_kerRepresentation_sub_cokerRepresentation_eq σ hπu hρu
    hFredholm hs hx hy

end Adjoint

end ContIntertwiningMap
