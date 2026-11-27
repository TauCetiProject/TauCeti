/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import TauCeti.Algebra.Lie.DirectSum
public import TauCeti.LinearAlgebra.Projection
import TauCeti.Algebra.Lie.Basic

/-!
# An internal direct sum of Lie submodules is an external one

A family `N : ι → LieSubmodule R L M` whose underlying submodules decompose `M`
(`DirectSum.IsInternal`) presents `M` as the external direct sum `⨁ i, N i`, which carries
Mathlib's Lie module structure on a direct sum. This file records the comparison: the sum map
`⨁ i, N i → M` is a morphism of Lie modules (`DirectSum.coeLieModuleHom`), and it is an equivalence
exactly when the decomposition is internal (`DirectSum.lieModuleEquivOfIsInternal`).

`DirectSum.IsInternal` is a statement about the underlying `Submodule`s, so it carries no
equivariance on its own; that is what is added here. With the equivalence in hand, a construction
applied to `M` can be computed summand by summand, which is how the multiplicity of an irreducible
in `M` is read off a decomposition of `M` into irreducibles in
`TauCeti/Algebra/Lie/Multiplicity.lean`. For a Lie algebra decomposed into Lie ideals, it also
assembles automorphisms of the summands into an automorphism of the whole algebra
(`LieEquiv.ofIsInternal`), which applies to the simple ideals of a semisimple Lie algebra
(`LieAlgebra.IsSemisimple.isInternal_atoms` in `TauCeti/Algebra/Lie/Submodule/Decomposition.lean`).

The file also proves the **regrouping theorem**
`DirectSum.nonempty_lieModuleEquiv_sigma_of_isInternal`: a decomposition of `M` whose summands are
labelled by a map `c : ι → σ`, the summand `N i` being equivalent to a fixed module `S (c i)`,
rewrites as `M ≃ ⨁_{s} S s ^ m s` with `m s` the number of indices carrying the label `s`. It is
the shape in which a decomposition into irreducibles is packaged once the summands are named: `σ`
is a set of names for the irreducibles, `c` sends a summand to the name of its isomorphism class,
and `m` is the multiplicity.

## Main definitions

* `DirectSum.coeLieModuleHom`: the sum map `⨁ i, N i →ₗ⁅R,L⁆ M`, refining Mathlib's
  `DirectSum.coeLinearMap`.
* `DirectSum.lieModuleEquivOfIsInternal`: the resulting equivalence of Lie modules
  `⨁ i, N i ≃ₗ⁅R,L⁆ M`, for an internal decomposition.
* `LieEquiv.ofIsInternal`: the automorphism of a Lie algebra `L` acting by `θ i` on the summand
  `I i` of an internal direct sum of Lie ideals.

## Main results

* `DirectSum.coeLieModuleHom_toLinearMap` and `DirectSum.coeLieModuleHom_bijective_iff`: the sum
  map refines `DirectSum.coeLinearMap`, so its bijectivity is `DirectSum.IsInternal`.
* `DirectSum.IsInternal.lieModuleProjection`: the canonical equivariant projection onto one
  summand, included back into the ambient module.
* `DirectSum.IsInternal.sum_lieModuleProjection_apply`: over a finite index type these projections
  sum to the identity.
* `DirectSum.nonempty_lieModuleEquiv_sigma_of_isInternal`: **an internal decomposition regrouped by
  the labels of its summands.**
* `TauCeti.LieModule.finrank_lieModuleHom_eq_sum_of_isInternal`: the finrank of a morphism space
  is additive over an internal decomposition of its target.
* `DirectSum.IsInternal.lieSubmodule_disjoint`, `DirectSum.IsInternal.lieSubmodule_induction`:
  distinct summands meet trivially, and a predicate holding at `0` and on every summand and closed
  under addition holds everywhere.
* `DirectSum.sum_support_lieModuleEquivOfIsInternal_symm`: an element is the sum of its components
  in the summands.
* `LieEquiv.eq_ofIsInternal_iff`: `LieEquiv.ofIsInternal` is the unique linear map acting by
  `θ i` on each summand; `LieEquiv.ofIsInternal_refl`, `LieEquiv.ofIsInternal_trans` and
  `LieEquiv.ofIsInternal_symm` make the assembly compatible with identity, composition and inverse.

## Applications

The multiplicity `LieModule.isotypicMultiplicity` counts the summands of a decomposition of `M` into
irreducibles; the decompositions it counts are produced by `TauCeti.exists_isInternal_isIrreducible`
of `TauCeti/Algebra/Lie/Submodule/Decomposition.lean`, in exactly the `DirectSum.IsInternal` form
consumed here.
-/

public section

open scoped DirectSum

universe u v w w₁ w₂ w₃ w₄

namespace DirectSum

variable {R : Type u} {L : Type v} {M : Type w} {ι : Type w₁} [dec_ι : DecidableEq ι]
variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M] [LieRingModule L M]

section Coercion

variable (N : ι → LieSubmodule R L M)

/-- **The sum map of a family of Lie submodules**, `⨁ i, N i → M`, as a morphism of Lie modules.
Its underlying linear map is `DirectSum.coeLinearMap`
(`DirectSum.coeLieModuleHom_toLinearMap`), so `DirectSum.IsInternal` is exactly the statement that
it is bijective. -/
noncomputable def coeLieModuleHom : (⨁ i, N i) →ₗ⁅R,L⁆ M :=
  { coeLinearMap (fun i ↦ (N i).toSubmodule) with
    map_lie' := by
      intro x m
      simp only [LinearMap.toFun_eq_coe]
      induction m using DirectSum.induction_on with
      | zero => simp
      | of i y =>
        -- The inclusion of a summand is a morphism of Lie modules, and it is `DirectSum.of`.
        have hlie : ⁅x, of (fun i ↦ (N i : Type w)) i y⁆
            = of (fun i ↦ (N i : Type w)) i ⁅x, y⁆ := by
          simpa only [lieModuleOf_apply] using
            ((lieModuleOf R ι L (fun i ↦ (N i : Type w)) i).map_lie x y).symm
        -- `DirectSum.coeLinearMap_of` reads the type family off `A`, so it needs restating over
        -- `fun i ↦ (N i : Type w)` before it can be rewritten with here.
        have key : ∀ (j : ι) (z : N j),
            coeLinearMap (fun i ↦ (N i).toSubmodule) (of (fun i ↦ (N i : Type w)) j z) = (z : M) :=
          fun j z ↦ coeLinearMap_of (fun i ↦ (N i).toSubmodule) j z
        rw [hlie, key, key]
        simp
      | add a b ha hb => simp [ha, hb] }

/-- The underlying linear map of the sum map of a family of Lie submodules is Mathlib's
`DirectSum.coeLinearMap` of the underlying submodules. -/
@[simp]
theorem coeLieModuleHom_toLinearMap :
    (coeLieModuleHom N : (⨁ i, N i) →ₗ[R] M) = coeLinearMap fun i ↦ (N i).toSubmodule :=
  (rfl)

@[simp]
theorem coeLieModuleHom_of (i : ι) (y : N i) :
    coeLieModuleHom N (of (fun i ↦ (N i : Type w)) i y) = (y : M) :=
  coeLinearMap_of (fun i ↦ (N i).toSubmodule) i y

/-- The sum map of a family of Lie submodules is bijective exactly when the family decomposes `M`
internally: by `DirectSum.coeLieModuleHom_toLinearMap` the two statements are about the same
underlying map. -/
theorem coeLieModuleHom_bijective_iff :
    Function.Bijective (coeLieModuleHom N) ↔ IsInternal fun i ↦ (N i).toSubmodule := by
  -- The preceding lemma equates bundled linear maps, whereas `Function.Bijective` exposes their
  -- coerced functions, so transport that equality across the coercion before applying `Iff.rfl`.
  rw [show ⇑(coeLieModuleHom N) = ⇑(coeLinearMap fun i ↦ (N i).toSubmodule) from
    congrArg DFunLike.coe (coeLieModuleHom_toLinearMap N)]
  exact Iff.rfl

/-- **An internal direct sum of Lie submodules, as an external one.** A family of Lie submodules
whose underlying submodules decompose `M` presents `M` as the direct sum of the family, as Lie
modules. -/
noncomputable def lieModuleEquivOfIsInternal (h : IsInternal fun i ↦ (N i).toSubmodule) :
    (⨁ i, N i) ≃ₗ⁅R,L⁆ M :=
  TauCeti.LieModuleEquiv.ofBijective (coeLieModuleHom N)
    ((coeLieModuleHom_bijective_iff N).mpr h)

@[simp]
theorem lieModuleEquivOfIsInternal_apply (h : IsInternal fun i ↦ (N i).toSubmodule)
    (m : ⨁ i, N i) : lieModuleEquivOfIsInternal N h m = coeLieModuleHom N m :=
  TauCeti.LieModuleEquiv.ofBijective_apply _ _ _

/-- The underlying linear equivalence of the internal Lie-module decomposition is the canonical
equivalence supplied by `DirectSum.IsInternal`. -/
theorem lieModuleEquivOfIsInternal_toLinearEquiv
    (h : IsInternal fun i ↦ (N i).toSubmodule) :
    (lieModuleEquivOfIsInternal N h : (⨁ i, N i) ≃ₗ[R] M) =
      LinearEquiv.ofBijective (coeLinearMap fun i ↦ (N i).toSubmodule) h := by
  ext m
  exact lieModuleEquivOfIsInternal_apply N h m

end Coercion

section Projection

variable {N : ι → LieSubmodule R L M}

/-- **The canonical projection onto an internal Lie-module summand.** It extracts one component
through the internal direct-sum equivalence and includes that component back into the ambient
module. -/
noncomputable def IsInternal.lieModuleProjection
    (h : IsInternal fun i ↦ (N i).toSubmodule) (i : ι) : M →ₗ⁅R,L⁆ M :=
  (N i).incl.comp
    ((lieModuleComponent R ι L (fun j ↦ ↥(N j)) i).comp
      (lieModuleEquivOfIsInternal N h).symm)

/-- Applying the canonical projection returns the selected internal direct-sum component. -/
theorem IsInternal.lieModuleProjection_apply
    (h : IsInternal fun i ↦ (N i).toSubmodule) (i : ι) (m : M) :
    h.lieModuleProjection i m =
      (((LinearEquiv.ofBijective (coeLinearMap fun j ↦ (N j).toSubmodule)
        h).symm m i : N i) : M) := by
  simp only [IsInternal.lieModuleProjection, LieModuleHom.comp_apply,
    LieSubmodule.incl_apply, lieModuleComponent_apply]
  have he := congrArg LinearEquiv.symm (lieModuleEquivOfIsInternal_toLinearEquiv N h)
  exact congrArg (fun z : ⨁ i, N i ↦ ((z i : N i) : M)) (DFunLike.congr_fun he m)

/-- The underlying linear map of the equivariant summand projection is the canonical projection
of the underlying internal direct sum, followed by the summand inclusion. -/
theorem IsInternal.lieModuleProjection_toLinearMap
    (h : IsInternal fun i ↦ (N i).toSubmodule) (i : ι) :
    (h.lieModuleProjection i : M →ₗ[R] M) =
      (N i).toSubmodule.subtype.comp
        (TauCeti.internalProjection h.submodule_iSupIndep h.submodule_iSup_eq_top i) := by
  apply LinearMap.ext
  intro m
  rw [LieModuleHom.coe_toLinearMap (h.lieModuleProjection i),
    IsInternal.lieModuleProjection_apply h i m, LinearMap.comp_apply]
  exact IsInternal.coe_ofBijective_coeLinearMap_symm_apply_eq_internalProjection
    h i m

/-- The canonical projection fixes every element of the selected summand. -/
@[simp]
theorem IsInternal.lieModuleProjection_apply_of_mem
    (h : IsInternal fun i ↦ (N i).toSubmodule) (i : ι) {m : M} (hm : m ∈ N i) :
    h.lieModuleProjection i m = m := by
  have he := congrArg (fun f : M →ₗ[R] M ↦ f m)
    (IsInternal.lieModuleProjection_toLinearMap h i)
  rw [LinearMap.comp_apply,
    TauCeti.internalProjection_apply_of_mem (Q := fun k ↦ (N k).toSubmodule)
      h.submodule_iSupIndep h.submodule_iSup_eq_top hm] at he
  exact he

/-- The canonical projection vanishes on every other summand. -/
@[simp]
theorem IsInternal.lieModuleProjection_apply_of_ne
    (h : IsInternal fun i ↦ (N i).toSubmodule) {i j : ι} (hji : j ≠ i)
    (m : N j) : h.lieModuleProjection i (m : M) = 0 := by
  have he := congrArg (fun f : M →ₗ[R] M ↦ f (m : M))
    (IsInternal.lieModuleProjection_toLinearMap h i)
  rw [LinearMap.comp_apply,
    TauCeti.internalProjection_apply_of_ne (Q := fun k ↦ (N k).toSubmodule)
      h.submodule_iSupIndep h.submodule_iSup_eq_top hji m] at he
  exact he

/-- The canonical projection is idempotent. -/
@[simp]
theorem IsInternal.lieModuleProjection_apply_apply
    (h : IsInternal fun i ↦ (N i).toSubmodule) (i : ι) (m : M) :
    h.lieModuleProjection i (h.lieModuleProjection i m) = h.lieModuleProjection i m := by
  apply h.lieModuleProjection_apply_of_mem
  rw [h.lieModuleProjection_apply]
  exact Subtype.property _

/-- The range of the canonical projection is exactly its selected summand. -/
@[simp]
theorem IsInternal.lieModuleProjection_range
    (h : IsInternal fun i ↦ (N i).toSubmodule) (i : ι) :
    (h.lieModuleProjection i).range = N i := by
  apply le_antisymm
  · rintro _ ⟨m, rfl⟩
    rw [h.lieModuleProjection_apply]
    exact Subtype.property _
  · intro m hm
    exact ⟨m, h.lieModuleProjection_apply_of_mem i hm⟩

end Projection

/-- Over a finite index type the equivariant projections onto the summands sum to the identity. -/
theorem IsInternal.sum_lieModuleProjection_apply [Fintype ι]
    {N : ι → LieSubmodule R L M} (h : IsInternal fun i ↦ (N i).toSubmodule) (m : M) :
    ∑ i, h.lieModuleProjection i m = m := by
  calc
    ∑ i, h.lieModuleProjection i m =
        ∑ i, ((TauCeti.internalProjection h.submodule_iSupIndep
          h.submodule_iSup_eq_top i m : (N i).toSubmodule) : M) := by
      apply Finset.sum_congr rfl
      intro i _
      exact LinearMap.congr_fun (h.lieModuleProjection_toLinearMap i) m
    _ = m := TauCeti.sum_coe_internalProjection
      h.submodule_iSupIndep h.submodule_iSup_eq_top m

/-- **An internal decomposition regrouped by the labels of its summands.** Suppose the Lie
submodules `N i` decompose `M` internally, that each `N i` is equivalent to a member `S (c i)` of a
family of Lie modules indexed by `σ`, and that `m s` counts the indices labelled `s`. Then `M` is
the direct sum, over the pairs of a label `s` and a counter in `Fin (m s)`, of `S s`.

Only `Nonempty` is asserted: the equivalence depends on the labelling and on the choice of an
equivalence `N i ≃ S (c i)` for each `i`, so there is no canonical one to name. -/
theorem nonempty_lieModuleEquiv_sigma_of_isInternal (N : ι → LieSubmodule R L M)
    [Finite ι] {σ : Type w₃} {S : σ → Type w₄}
    [∀ s, AddCommGroup (S s)] [∀ s, Module R (S s)] [∀ s, LieRingModule L (S s)] {m : σ → ℕ}
    (h : IsInternal fun i ↦ (N i).toSubmodule) (c : ι → σ)
    (hc : ∀ i, Nonempty ((N i : Type w) ≃ₗ⁅R,L⁆ S (c i)))
    (hcard : ∀ s, Nat.card {i // c i = s} = m s) :
    Nonempty (M ≃ₗ⁅R,L⁆ ⨁ q : Σ s : σ, Fin (m s), S q.1) := by
  classical
  -- Reindex `ι` by the label together with a counter, using that the fibre of `c` over `s` has
  -- `m s` elements.
  let g : (Σ s : σ, Fin (m s)) ≃ ι :=
    (Equiv.sigmaCongrRight fun s ↦ (Finite.equivFinOfCardEq (hcard s)).symm).trans
      (Equiv.sigmaFiberEquiv c)
  -- `Equiv.sigmaFiberEquiv` is the projection to the element of the fibre, whose defining
  -- property is that its label is `q.1`.
  have hg : ∀ q : Σ s : σ, Fin (m s), c (g q) = q.1 := fun q ↦ by
    simpa only [g, Equiv.trans_apply, Equiv.sigmaCongrRight_apply,
      Equiv.sigmaFiberEquiv_apply] using ((Finite.equivFinOfCardEq (hcard q.1)).symm q.2).property
  have e : ∀ q : Σ s : σ, Fin (m s), (N (g q) : Type w) ≃ₗ⁅R,L⁆ S q.1 := fun q ↦
    (hg q ▸ hc (g q) : Nonempty ((N (g q) : Type w) ≃ₗ⁅R,L⁆ S q.1)).some
  exact ⟨(lieModuleEquivOfIsInternal N h).symm.trans
    ((lieModuleEquivCongrLeft R L (P := fun i ↦ (N i : Type w)) g.symm).trans
      (lieModuleEquivCongrRight e))⟩

section Summands

variable {N : ι → LieSubmodule R L M} (h : IsInternal fun i ↦ (N i).toSubmodule)
include h

/-- Distinct summands of an internal direct sum of Lie submodules have trivial intersection. -/
theorem IsInternal.lieSubmodule_disjoint {i j : ι} (hij : i ≠ j) : Disjoint (N i) (N j) :=
  (LieSubmodule.iSupIndep_toSubmodule.mp h.submodule_iSupIndep).pairwiseDisjoint hij

/-- **Induction over an internal direct sum of Lie submodules.** A predicate on `M` that holds on
every summand and at `0`, and is closed under addition, holds everywhere. -/
theorem IsInternal.lieSubmodule_induction {motive : M → Prop} (mem : ∀ i, ∀ x ∈ N i, motive x)
    (zero : motive 0) (add : ∀ x y, motive x → motive y → motive (x + y)) (x : M) : motive x :=
  Submodule.iSup_induction _ (motive := motive) (h.submodule_iSup_eq_top ▸ Submodule.mem_top) mem
    zero add

/-- An element of an internal direct sum of Lie submodules is the sum of its components. -/
theorem sum_support_lieModuleEquivOfIsInternal_symm [∀ i (x : N i), Decidable (x ≠ 0)] (x : M) :
    ∑ i ∈ ((lieModuleEquivOfIsInternal N h).symm x).support,
      (((lieModuleEquivOfIsInternal N h).symm x i : N i) : M) = x := by
  conv_rhs => rw [← (lieModuleEquivOfIsInternal N h).apply_symm_apply x,
    ← sum_support_of ((lieModuleEquivOfIsInternal N h).symm x), map_sum]
  simp only [lieModuleEquivOfIsInternal_apply, coeLieModuleHom_of]

end Summands

end DirectSum

namespace LieEquiv

open DirectSum

section OfIsInternal

variable {R L ι : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [DecidableEq ι]
  {I : ι → LieIdeal R L} (h : IsInternal fun i ↦ (I i).toSubmodule)
  (θ : ∀ i, I i ≃ₗ⁅R⁆ I i)

/-- The identification of the external direct sum of the summands of an internal direct sum with
`L`. -/
private noncomputable abbrev sumEquiv : (⨁ i, I i) ≃ₗ[R] L :=
  (lieModuleEquivOfIsInternal I h).toLinearEquiv

/-- The linear automorphism of `L` acting by `θ i` on each summand of an internal direct sum. -/
private noncomputable def linearOfIsInternal : L ≃ₗ[R] L :=
  (sumEquiv h).symm ≪≫ₗ congrLinearEquiv (fun i ↦ (θ i).toLinearEquiv) ≪≫ₗ sumEquiv h

private theorem linearOfIsInternal_apply_of_mem {i : ι} {x : L} (hx : x ∈ I i) :
    linearOfIsInternal h θ x = θ i ⟨x, hx⟩ := by
  have hs : (sumEquiv h).symm x = of (fun i ↦ (I i : Type _)) i ⟨x, hx⟩ := by
    rw [LinearEquiv.symm_apply_eq, LieModuleEquiv.coe_toLinearEquiv,
      lieModuleEquivOfIsInternal_apply, coeLieModuleHom_of]
  simp [linearOfIsInternal, hs, coe_congrLinearEquiv, lmap_of]

private theorem linearOfIsInternal_mem {i : ι} {x : L} (hx : x ∈ I i) :
    linearOfIsInternal h θ x ∈ I i := by
  rw [linearOfIsInternal_apply_of_mem h θ hx]
  exact (θ i ⟨x, hx⟩).property

private theorem linearOfIsInternal_map_lie (x y : L) :
    linearOfIsInternal h θ ⁅x, y⁆ = ⁅linearOfIsInternal h θ x, linearOfIsInternal h θ y⁆ := by
  induction x using h.lieSubmodule_induction with
  | zero => simp
  | add x x' hx hx' => simp only [add_lie, map_add, hx, hx']
  | mem i x hx =>
    induction y using h.lieSubmodule_induction with
    | zero => simp
    | add y y' hy hy' => simp only [lie_add, map_add, hy, hy']
    | mem j y hy =>
      by_cases hij : i = j
      · subst hij
        rw [linearOfIsInternal_apply_of_mem h θ (lie_mem_left R L (I i) x y hx),
          linearOfIsInternal_apply_of_mem h θ hx, linearOfIsInternal_apply_of_mem h θ hy]
        exact congrArg Subtype.val ((θ i).map_lie ⟨x, hx⟩ ⟨y, hy⟩)
      · rw [LieIdeal.lie_eq_zero_of_disjoint (h.lieSubmodule_disjoint hij) hx hy,
          LieIdeal.lie_eq_zero_of_disjoint (h.lieSubmodule_disjoint hij)
            (linearOfIsInternal_mem h θ hx) (linearOfIsInternal_mem h θ hy), map_zero]

/-- The Lie algebra automorphism of `L` acting by `θ i` on the summand `I i` of an internal direct
sum of Lie ideals. -/
noncomputable def ofIsInternal : L ≃ₗ⁅R⁆ L :=
  { linearOfIsInternal h θ with
    map_lie' := fun {x y} ↦ linearOfIsInternal_map_lie h θ x y }

/-- `LieEquiv.ofIsInternal` acts by `θ i` on the summand `I i`. -/
theorem ofIsInternal_apply_of_mem {i : ι} {x : L} (hx : x ∈ I i) :
    ofIsInternal h θ x = θ i ⟨x, hx⟩ :=
  linearOfIsInternal_apply_of_mem h θ hx

/-- `LieEquiv.ofIsInternal` acts by `θ i` on the summand `I i`. -/
@[simp]
theorem ofIsInternal_apply_coe {i : ι} (x : I i) : ofIsInternal h θ x = θ i x :=
  ofIsInternal_apply_of_mem h θ x.property

/-- `LieEquiv.ofIsInternal` is the unique linear map acting by `θ i` on each summand `I i`. -/
theorem eq_ofIsInternal_iff (f : L →ₗ[R] L) :
    f = (ofIsInternal h θ : L →ₗ[R] L) ↔ ∀ i (x : I i), f x = θ i x := by
  refine ⟨fun hf i x ↦ by rw [hf]; exact ofIsInternal_apply_coe h θ x, fun hf ↦ ?_⟩
  refine LinearMap.ext fun x ↦ ?_
  induction x using h.lieSubmodule_induction with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, hx, hx']
  | mem i x hx => exact (hf i ⟨x, hx⟩).trans (ofIsInternal_apply_of_mem h θ hx).symm

/-- Assembling the identities of the summands gives the identity. -/
@[simp]
theorem ofIsInternal_refl : ofIsInternal h (fun _ ↦ LieEquiv.refl) = LieEquiv.refl :=
  LieEquiv.ext fun x ↦ (LinearMap.congr_fun ((eq_ofIsInternal_iff h _ _).mpr
    fun i x ↦ by simp) x).symm

/-- Assembling automorphisms of the summands is compatible with composition. -/
@[simp]
theorem ofIsInternal_trans (φ : ∀ i, I i ≃ₗ⁅R⁆ I i) :
    (ofIsInternal h θ).trans (ofIsInternal h φ) = ofIsInternal h (fun i ↦ (θ i).trans (φ i)) :=
  LieEquiv.ext fun x ↦ LinearMap.congr_fun ((eq_ofIsInternal_iff h _ _).mpr
    fun i x ↦ by simp [LieEquiv.trans_apply]) x

/-- Assembling automorphisms of the summands is compatible with inversion. -/
@[simp]
theorem ofIsInternal_symm : (ofIsInternal h θ).symm = ofIsInternal h (fun i ↦ (θ i).symm) := by
  have hrefl : (ofIsInternal h θ).trans (ofIsInternal h fun i ↦ (θ i).symm) = LieEquiv.refl := by
    simp only [ofIsInternal_trans, LieEquiv.self_trans_symm, ofIsInternal_refl]
  ext x
  simpa [-ofIsInternal_trans] using (DFunLike.congr_fun hrefl ((ofIsInternal h θ).symm x)).symm

end OfIsInternal

end LieEquiv

namespace TauCeti.LieModule

open Module (finrank)

variable {K : Type u} {L : Type v} {M : Type w} {ι : Type w₁} [DecidableEq ι] [Fintype ι]
variable [Field K] [LieRing L] [LieAlgebra K L]
variable [AddCommGroup M] [Module K M] [LieRingModule L M] [_root_.LieModule K L M]
variable (S : Type w₂) [AddCommGroup S] [Module K S] [LieRingModule L S]

/-- **Additivity of the morphism space over a decomposition of the target.** If the Lie submodules
`N i` decompose `M` and every component morphism space is finite-dimensional, the finrank of
`S →ₗ⁅K,L⁆ M` is the sum of the finranks of the `S →ₗ⁅K,L⁆ N i`. -/
theorem finrank_lieModuleHom_eq_sum_of_isInternal (N : ι → LieSubmodule K L M)
    (h : DirectSum.IsInternal fun i ↦ (N i).toSubmodule)
    (hfin : ∀ i, FiniteDimensional K (S →ₗ⁅K,L⁆ N i)) :
    finrank K (S →ₗ⁅K,L⁆ M) = ∑ i, finrank K (S →ₗ⁅K,L⁆ N i) := by
  let _ : ∀ i, FiniteDimensional K (S →ₗ⁅K,L⁆ N i) := hfin
  rw [← ((DirectSum.lieModuleEquivOfIsInternal N h).congrRight (M := S)).finrank_eq,
    (lieModuleHomDirectSumEquiv K L S fun i ↦ (N i : Type w)).finrank_eq,
    Module.finrank_pi_fintype]

end TauCeti.LieModule
