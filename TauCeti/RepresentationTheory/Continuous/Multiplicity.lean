/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.ClosedRange
public import TauCeti.Analysis.Fredholm.ContinuousFamily
public import TauCeti.RepresentationTheory.Continuous.Intertwining
public import TauCeti.RepresentationTheory.Continuous.Invariants
public import TauCeti.RepresentationTheory.Continuous.KernelCokernel
public import TauCeti.RepresentationTheory.Continuous.LinHom

/-!
# Equivariant Fredholm operators on multiplicity spaces

Let `π` and `ρ` be representations of a group `G` on Banach spaces `E` and `F`, and let `σ` be a
representation on a finite-dimensional space `V`. The continuous intertwiners `σ →ⁱL π` form the
invariant subspace `(linHom σ π).invariants` of the operator space `V →L[𝕜] E`, a Banach space;
when `G` is compact and `σ` is irreducible, its dimension is the multiplicity of `σ` in `π`. An
intertwining map `T : π →ⁱL ρ` acts on these multiplicity spaces by composition, `S ↦ T ∘ S`; this
is `(T.compLinHom σ).mapInvariants`.

This file shows that the action of `T` on multiplicity spaces computes the multiplicities of `σ`
in the kernel and in the cokernel of `T`. For every `T`, the kernel of the action is the space of
intertwiners from `σ` into the kernel representation of `T`. For unitary representations on
Hilbert spaces and `T` with closed range, its cokernel is the space of intertwiners from `σ` into
the cokernel representation of `T`. Two lifting properties give this: an intertwiner with values in
the range of `T` factors through `T`, through the inverse of `T` on the orthogonal complement of its
kernel, which is invariant by unitarity; and an intertwiner into the cokernel lifts to `ρ` through
the orthogonal complement of the range. Consequently, if `T` is Fredholm then so is its action on
multiplicity spaces, with index `dim Hom_G(σ, ker T) - dim Hom_G(σ, coker T)`.

The action is the restriction to invariants of the continuous linear map `T ↦ (S ↦ T ∘ S)`, so it
carries norm-continuous families of equivariant operators to norm-continuous families. With the
local constancy of the Fredholm index, along a norm-continuous family of equivariant Fredholm
operators on a preconnected parameter set the difference of the multiplicities of `σ` in the kernel
and in the cokernel is constant. This is the homotopy invariance of the equivariant index
`[ker T] - [coker T]`, read one multiplicity at a time.

## Main definitions

* `ContIntertwiningMap.compLinHom`: composition with `T : π →ⁱL ρ`, as an intertwiner
  `linHom σ π →ⁱL linHom σ ρ` of Hom representations.
* `ContIntertwiningMap.kerCompLinHomEquiv`: the kernel of the action of `T` on multiplicity spaces
  is the space of intertwiners `σ →ⁱL T.kerRepresentation`.
* `ContIntertwiningMap.cokerCompLinHomEquiv`: for unitary representations on Hilbert spaces and a
  closed range, its cokernel is the space of intertwiners `σ →ⁱL T.cokerRepresentation`.

## Main statements

* `ContIntertwiningMap.mem_ker_mapInvariants_compLinHom_iff`,
  `ContIntertwiningMap.mem_range_mapInvariants_compLinHom_iff`: an intertwiner lies in the kernel,
  respectively the range, of the action of `T` exactly when its values lie in `ker T`, respectively
  in the range of `T`.
* `ContinuousOn.mapInvariants_compLinHom`: the action depends continuously on `T`.
* `ContIntertwiningMap.exists_comp_eq`: an intertwiner from a finite-dimensional representation with
  values in the range of `T` factors through `T`.
* `ContIntertwiningMap.isFredholm_mapInvariants_compLinHom`,
  `ContIntertwiningMap.index_mapInvariants_compLinHom`: the action of a Fredholm `T` is Fredholm,
  of index `finrank (σ →ⁱL T.kerRepresentation) - finrank (σ →ⁱL T.cokerRepresentation)`.
* `ContinuousOn.finrank_contIntertwiningMap_kerRepresentation_sub_cokerRepresentation_eq`: this
  difference of multiplicities is constant along a continuous family of equivariant Fredholm
  operators on a preconnected parameter set.

## References

* M. F. Atiyah and I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  484–530.
-/

public section

open ContRepresentation Module

namespace ContIntertwiningMap

/-! ### The action on multiplicity spaces -/

section Normed

variable {𝕜 G V E F : Type*} [NontriviallyNormedField 𝕜] [Group G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (σ : ContRepresentation 𝕜 G V) {π : ContRepresentation 𝕜 G E} {ρ : ContRepresentation 𝕜 G F}

/-- **Composition with an intertwining map.** For `T : π →ⁱL ρ`, composition `S ↦ T ∘ S` on the
operators out of `V` intertwines the Hom representations `linHom σ π` and `linHom σ ρ`. On their
invariants, `(T.compLinHom σ).mapInvariants` sends an intertwiner `σ →ⁱL π` to its composite with
`T`: this is the action of `T` on the multiplicity spaces of `σ`. -/
noncomputable def compLinHom (T : π →ⁱL ρ) : linHom σ π →ⁱL linHom σ ρ where
  toContinuousLinearMap := ContinuousLinearMap.compL 𝕜 V E F T.toContinuousLinearMap
  isIntertwining' g := by
    ext S v
    simp [toContinuousLinearMap_apply, T.isIntertwining]

/-- Composition with `T` sends an operator `S` to `T ∘ S`. -/
@[simp]
theorem compLinHom_apply (T : π →ⁱL ρ) (S : V →L[𝕜] E) :
    T.compLinHom σ S = T.toContinuousLinearMap ∘L S :=
  (rfl)

/-- On multiplicity spaces, composition with `T` sends an intertwiner `S` to `T ∘ S`. -/
@[simp]
theorem coe_mapInvariants_compLinHom_apply (T : π →ⁱL ρ) (S : (linHom σ π).invariants) :
    ((T.compLinHom σ).mapInvariants S : V →L[𝕜] F) = T.toContinuousLinearMap ∘L S :=
  (rfl)

variable {X : Type*} [TopologicalSpace X]

/-- The action on multiplicity spaces depends continuously on the operator: a family of
intertwining maps continuous on `s` for the operator topology acts on the multiplicity spaces of
`σ` by a family continuous on `s`. -/
theorem _root_.ContinuousOn.mapInvariants_compLinHom {A : X → π →ⁱL ρ} {s : Set X}
    (hA : ContinuousOn (fun x ↦ (A x).toContinuousLinearMap) s) :
    ContinuousOn (fun x ↦ ((A x).compLinHom σ).mapInvariants) s := by
  -- Followed by the inclusion of the target invariants, which induces the operator topology, the
  -- action is composition with `A x` restricted to the source invariants.
  rw [(ContinuousLinearMap.isInducing_postcomp (linHom σ ρ).invariants.subtypeL
    Topology.IsInducing.subtypeVal).continuousOn_iff]
  exact ((ContinuousLinearMap.precomp (V →L[𝕜] F)
    (linHom σ π).invariants.subtypeL).continuous.comp
      (ContinuousLinearMap.compL 𝕜 V E F).continuous).comp_continuousOn hA

/-- The action on multiplicity spaces of a family of intertwining maps, continuous for the operator
topology, is continuous. -/
theorem _root_.Continuous.mapInvariants_compLinHom {A : X → π →ⁱL ρ}
    (hA : Continuous fun x ↦ (A x).toContinuousLinearMap) :
    Continuous fun x ↦ ((A x).compLinHom σ).mapInvariants :=
  continuousOn_univ.mp (hA.continuousOn.mapInvariants_compLinHom σ)

/-- An intertwiner is killed by composition with `T` exactly when it takes values in `ker T`. -/
theorem mem_ker_mapInvariants_compLinHom_iff (T : π →ⁱL ρ) {S : (linHom σ π).invariants} :
    S ∈ (T.compLinHom σ).mapInvariants.ker ↔
      ∀ v, (S : V →L[𝕜] E) v ∈ T.toContinuousLinearMap.ker := by
  simp [LinearMap.mem_ker, Subtype.ext_iff, ContinuousLinearMap.ext_iff]

/-- **The kernel of the action on multiplicity spaces.** An intertwiner `S : σ →ⁱL π` is killed by
composition with `T` exactly when it takes values in `ker T`, so the kernel of the action of `T` on
the multiplicity spaces of `σ` is the space of intertwiners from `σ` into the kernel representation
of `T`. -/
noncomputable def kerCompLinHomEquiv (T : π →ⁱL ρ) :
    (T.compLinHom σ).mapInvariants.ker ≃ₗ[𝕜] (σ →ⁱL T.kerRepresentation) where
  toFun S :=
    { toContinuousLinearMap := (S.1.1 : V →L[𝕜] E).codRestrict _
        ((mem_ker_mapInvariants_compLinHom_iff σ T).1 S.2)
      isIntertwining' g := by
        ext v
        simpa using congr($((mem_linHom_invariants_iff_isIntertwining σ π _).1 S.1.2 g) v) }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun R :=
    ⟨⟨T.toContinuousLinearMap.ker.subtypeL ∘L R.toContinuousLinearMap,
        (mem_linHom_invariants_iff_isIntertwining σ π _).2 fun g ↦ by
          ext v
          simp [toContinuousLinearMap_apply, R.isIntertwining]⟩,
      (mem_ker_mapInvariants_compLinHom_iff σ T).2 fun v ↦ (R v).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The identification of the kernel with the intertwiners into `ker T` keeps the values. -/
@[simp]
theorem coe_kerCompLinHomEquiv_apply_apply (T : π →ⁱL ρ) (S : (T.compLinHom σ).mapInvariants.ker)
    (v : V) :
    (T.kerCompLinHomEquiv σ S v : E) = ((S : (linHom σ π).invariants) : V →L[𝕜] E) v :=
  (rfl)

/-- The inverse identification of the kernel with the intertwiners into `ker T` keeps the values. -/
@[simp]
theorem kerCompLinHomEquiv_symm_apply_apply (T : π →ⁱL ρ) (R : σ →ⁱL T.kerRepresentation)
    (v : V) :
    (((T.kerCompLinHomEquiv σ).symm R : (linHom σ π).invariants) : V →L[𝕜] E) v = R v :=
  (rfl)

end Normed

/-! ### Lifting intertwiners through an intertwining map -/

section Lift

variable {𝕜 G V E F : Type*} [RCLike 𝕜] [Group G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (σ : ContRepresentation 𝕜 G V) {π : ContRepresentation 𝕜 G E} {ρ : ContRepresentation 𝕜 G F}
  (T : π →ⁱL ρ)

/-- **Intertwiners into the range lift.** For a unitary representation `π` on a Hilbert space, an
intertwiner from a finite-dimensional representation `σ` whose values lie in the range of
`T : π →ⁱL ρ` factors through `T`. The lift sends `v` to the unique preimage of `S v` in the
orthogonal complement of `ker T`, which is invariant because `π` is unitary. -/
theorem exists_comp_eq (hπ : π.IsUnitary) {S : σ →ⁱL ρ}
    (hS : ∀ v, S v ∈ T.toContinuousLinearMap.range) : ∃ R : σ →ⁱL π, T.comp R = S := by
  set K := T.toContinuousLinearMap.ker
  have : CompleteSpace K := T.toContinuousLinearMap.isClosed_ker.completeSpace_coe
  -- `T` is injective on `Kᗮ`, and every value of `S` has a preimage there.
  have huniq {w w' : E} (hw : w ∈ Kᗮ) (hw' : w' ∈ Kᗮ) (h : T w = T w') : w = w' :=
    sub_eq_zero.1 <| Submodule.disjoint_def.1 K.orthogonal_disjoint _
      (by simp [K, LinearMap.mem_ker, toContinuousLinearMap_apply, h])
      (Kᗮ.sub_mem hw hw')
  have hpre (v : V) : ∃ w ∈ Kᗮ, T w = S v := by
    obtain ⟨w, hw⟩ := hS v
    refine ⟨w - K.starProjection w, K.sub_starProjection_mem_orthogonal w, ?_⟩
    have hK : T (K.starProjection w) = 0 := LinearMap.mem_ker.1 (K.starProjection_apply_mem w)
    rw [map_sub, hK, sub_zero]
    exact hw
  choose f hfK hf using hpre
  let f' : V →ₗ[𝕜] E :=
    { toFun := f
      map_add' v v' := huniq (hfK _) (Kᗮ.add_mem (hfK v) (hfK v')) (by simp [hf])
      map_smul' c v := huniq (hfK _) (Kᗮ.smul_mem c (hfK v)) (by simp [hf]) }
  have hKinv (g : G) (k : E) (hk : k ∈ K) : π g k ∈ K := by
    simp_all [K, LinearMap.mem_ker, toContinuousLinearMap_apply, T.isIntertwining]
  refine ⟨⟨LinearMap.toContinuousLinearMap f', fun g ↦ ?_⟩, ?_⟩
  · ext v
    exact huniq (hfK _) (hπ.apply_mem_orthogonal hKinv g (hfK v))
      (by simp [f', hf, S.isIntertwining, T.isIntertwining])
  · ext v
    exact hf v

/-- An intertwiner lies in the range of the action of `T` on multiplicity spaces exactly when it
takes values in the range of `T`, for `π` unitary on a Hilbert space and `σ` finite-dimensional. -/
theorem mem_range_mapInvariants_compLinHom_iff (hπ : π.IsUnitary)
    {S : (linHom σ ρ).invariants} :
    S ∈ (T.compLinHom σ).mapInvariants.range ↔
      ∀ v, (S : V →L[𝕜] F) v ∈ T.toContinuousLinearMap.range := by
  constructor
  · rintro ⟨R, rfl⟩ v
    exact ⟨_, rfl⟩
  · intro hS
    obtain ⟨R, hR⟩ := T.exists_comp_eq σ hπ
      (S := ⟨S, (mem_linHom_invariants_iff_isIntertwining σ ρ _).1 S.2⟩) hS
    refine ⟨⟨R.toContinuousLinearMap, toContinuousLinearMap_mem_invariants_linHom σ π R⟩, ?_⟩
    ext v
    exact congr($hR v)

end Lift

/-! ### The cokernel of the action on multiplicity spaces -/

section Cokernel

variable {𝕜 G V E F : Type*} [RCLike 𝕜] [Group G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  (σ : ContRepresentation 𝕜 G V) {π : ContRepresentation 𝕜 G E} {ρ : ContRepresentation 𝕜 G F}
  (T : π →ⁱL ρ)

/-- Composition of an intertwiner `σ →ⁱL ρ` with the quotient map onto the cokernel of `T`. -/
private noncomputable def toCoker :
    (linHom σ ρ).invariants →ₗ[𝕜] (σ →ⁱL T.cokerRepresentation) where
  toFun S :=
    { toContinuousLinearMap := T.toContinuousLinearMap.range.mkQL ∘L (S : V →L[𝕜] F)
      isIntertwining' g := by
        ext v
        have h := congr($((mem_linHom_invariants_iff_isIntertwining σ ρ _).1 S.2 g) v)
        simp only [ContinuousLinearMap.comp_apply] at h
        simp [h] }
  map_add' _ _ := by
    ext
    simp
  map_smul' _ _ := by
    ext
    simp

omit [FiniteDimensional 𝕜 V] [CompleteSpace E] in
private theorem toCoker_apply_apply (S : (linHom σ ρ).invariants) (v : V) :
    toCoker σ T S v = Submodule.Quotient.mk ((S : V →L[𝕜] F) v) :=
  (rfl)

private theorem ker_toCoker (hπ : π.IsUnitary) :
    (toCoker σ T).ker = (T.compLinHom σ).mapInvariants.range := by
  ext S
  rw [mem_range_mapInvariants_compLinHom_iff σ T hπ, LinearMap.mem_ker,
    ContIntertwiningMap.ext_iff, ContinuousLinearMap.ext_iff]
  simp only [toContinuousLinearMap_apply, toCoker_apply_apply, toContinuousLinearMap_zero,
    _root_.zero_apply, Submodule.Quotient.mk_eq_zero]

omit [FiniteDimensional 𝕜 V] [CompleteSpace E] in
private theorem toCoker_surjective (hρ : ρ.IsUnitary)
    [T.toContinuousLinearMap.range.HasOrthogonalProjection] :
    Function.Surjective (toCoker σ T) := by
  intro R
  let L : σ →ⁱL ρ :=
    { toContinuousLinearMap := T.toContinuousLinearMap.rangeᗮ.subtypeL ∘L
        ((T.cokerEquivOrthogonalRange hρ).toContIntertwiningMap.comp R).toContinuousLinearMap
      isIntertwining' g := by
        ext v
        have he := congr($((T.cokerEquivOrthogonalRange hρ).isIntertwining g) (R v))
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] at he
        simp [toContinuousLinearMap_apply, R.isIntertwining, he] }
  refine ⟨⟨L.toContinuousLinearMap, toContinuousLinearMap_mem_invariants_linHom σ ρ L⟩, ?_⟩
  ext v
  rw [toContinuousLinearMap_apply, toContinuousLinearMap_apply, toCoker_apply_apply]
  exact ((T.cokerEquivOrthogonalRange_symm_apply hρ _).symm.trans
    ((T.cokerEquivOrthogonalRange hρ).symm_apply_apply (R v)))

variable [T.toContinuousLinearMap.range.HasOrthogonalProjection]

/-- **The cokernel of the action on multiplicity spaces.** For unitary representations on Hilbert
spaces and `T` with a range admitting an orthogonal projection (for instance, a closed range in a
Hilbert space), the
cokernel of the action of `T` on the multiplicity spaces of `σ` is the space of intertwiners from
`σ` into the cokernel representation of `T`. The class of an intertwiner `S : σ →ⁱL ρ` goes to its
composite with the quotient map onto `F ⧸ range T`. -/
noncomputable def cokerCompLinHomEquiv (hπ : π.IsUnitary) (hρ : ρ.IsUnitary) :
    ((linHom σ ρ).invariants ⧸ (T.compLinHom σ).mapInvariants.range) ≃ₗ[𝕜]
      (σ →ⁱL T.cokerRepresentation) :=
  (Submodule.quotEquivOfEq _ _ (ker_toCoker σ T hπ).symm).trans
    ((toCoker σ T).quotKerEquivOfSurjective (toCoker_surjective σ T hρ))

/-- The identification of the cokernel with the intertwiners into `coker T` sends the class of `S`
to the composite of `S` with the quotient map. -/
@[simp]
theorem cokerCompLinHomEquiv_mk_apply (hπ : π.IsUnitary) (hρ : ρ.IsUnitary)
    (S : (linHom σ ρ).invariants) (v : V) :
    T.cokerCompLinHomEquiv σ hπ hρ (Submodule.Quotient.mk S) v =
      Submodule.Quotient.mk ((S : V →L[𝕜] F) v) :=
  (rfl)

end Cokernel

/-! ### Fredholm operators -/

section Fredholm

variable {𝕜 G V E F : Type*} [RCLike 𝕜] [Group G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  (σ : ContRepresentation 𝕜 G V) {π : ContRepresentation 𝕜 G E} {ρ : ContRepresentation 𝕜 G F}

/-- **The action of an equivariant Fredholm operator on multiplicity spaces is Fredholm.** For
unitary representations on Hilbert spaces and a Fredholm intertwining map `T`, the action of `T` on
the multiplicity spaces of a finite-dimensional `σ` is Fredholm. -/
theorem isFredholm_mapInvariants_compLinHom (hπ : π.IsUnitary) (hρ : ρ.IsUnitary) {T : π →ⁱL ρ}
    (hT : T.toContinuousLinearMap.IsFredholm) :
    (T.compLinHom σ).mapInvariants.IsFredholm := by
  have := hT.finite_ker
  have := hT.finite_coker
  have : CompleteSpace T.toContinuousLinearMap.range := hT.isClosed_range.completeSpace_coe
  have hker : FiniteDimensional 𝕜 (T.compLinHom σ).mapInvariants.ker :=
    (T.kerCompLinHomEquiv σ).symm.finiteDimensional
  have hcoker : FiniteDimensional 𝕜
      ((linHom σ ρ).invariants ⧸ (T.compLinHom σ).mapInvariants.range) :=
    (T.cokerCompLinHomEquiv σ hπ hρ).symm.finiteDimensional
  -- Naming the two carriers lets the normed structures of the invariants be found directly;
  -- unifying them from the goal instead unfolds the operator-space topology and times out.
  have h := ContinuousLinearMap.IsFredholm.of_finite_ker_coker (𝕜 := 𝕜)
    (E := (linHom σ π).invariants) (F := (linHom σ ρ).invariants)
  exact h (T.compLinHom σ).mapInvariants hker hcoker

/-- **The index of the action on multiplicity spaces.** For unitary representations on Hilbert
spaces and a Fredholm `T`, the action of `T` on the multiplicity spaces of a finite-dimensional `σ`
has index `dim Hom_G(σ, ker T) - dim Hom_G(σ, coker T)`, the difference of the multiplicities of
`σ` in the kernel and in the cokernel of `T` when `σ` is irreducible and `G` compact. -/
theorem index_mapInvariants_compLinHom (hπ : π.IsUnitary) (hρ : ρ.IsUnitary) {T : π →ⁱL ρ}
    (hT : T.toContinuousLinearMap.IsFredholm) :
    (T.compLinHom σ).mapInvariants.index =
      finrank 𝕜 (σ →ⁱL T.kerRepresentation) - finrank 𝕜 (σ →ⁱL T.cokerRepresentation) := by
  have : CompleteSpace T.toContinuousLinearMap.range := hT.isClosed_range.completeSpace_coe
  rw [ContinuousLinearMap.index_eq_finrank_sub, (T.kerCompLinHomEquiv σ).finrank_eq,
    (T.cokerCompLinHomEquiv σ hπ hρ).finrank_eq]

variable {X : Type*} [TopologicalSpace X]

/-- **Homotopy invariance of the multiplicities in the equivariant index.** Along a family of
intertwining maps between unitary representations on Hilbert spaces, continuous in operator norm
and Fredholm on a preconnected set `s`, the difference between the dimensions of the intertwiners
from a finite-dimensional `σ` into the kernel and into the cokernel is the same at every point of
`s`. For `G` compact and `σ` irreducible this is the difference of the multiplicities of `σ` in the
kernel and in the cokernel. -/
theorem _root_.ContinuousOn.finrank_contIntertwiningMap_kerRepresentation_sub_cokerRepresentation_eq
    (hπ : π.IsUnitary) (hρ : ρ.IsUnitary) {A : X → π →ⁱL ρ} {s : Set X}
    (hA : ContinuousOn (fun x ↦ (A x).toContinuousLinearMap) s)
    (hFredholm : ∀ x ∈ s, (A x).toContinuousLinearMap.IsFredholm) (hs : IsPreconnected s)
    {x y : X} (hx : x ∈ s) (hy : y ∈ s) :
    (finrank 𝕜 (σ →ⁱL (A x).kerRepresentation) : ℤ) -
        finrank 𝕜 (σ →ⁱL (A x).cokerRepresentation) =
      finrank 𝕜 (σ →ⁱL (A y).kerRepresentation) - finrank 𝕜 (σ →ⁱL (A y).cokerRepresentation) := by
  rw [← index_mapInvariants_compLinHom σ hπ hρ (hFredholm x hx),
    ← index_mapInvariants_compLinHom σ hπ hρ (hFredholm y hy)]
  -- As in `isFredholm_mapInvariants_compLinHom`, the carriers are named for elaboration.
  have h := ContinuousOn.index_eq_of_isPreconnected (K := 𝕜) (E := (linHom σ π).invariants)
    (F := (linHom σ ρ).invariants) (A := fun z ↦ ((A z).compLinHom σ).mapInvariants)
    (s := s)
  exact h (hA.mapInvariants_compLinHom σ)
    (fun z hz ↦ isFredholm_mapInvariants_compLinHom σ hπ hρ (hFredholm z hz)) hs hx hy

end Fredholm

end ContIntertwiningMap
