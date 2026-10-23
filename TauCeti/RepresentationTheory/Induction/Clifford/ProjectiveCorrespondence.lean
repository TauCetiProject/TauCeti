/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Clifford.TensorFactorization
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import TauCeti.RepresentationTheory.Irreducible

/-!
# Representations over `A` from projective representations of the inertia quotient

Let `N` be a normal subgroup of `G`, let `A` be a finite-dimensional representation of `N`, and
let `ρ` be a projective extension of `A` to its inertia group `T = inertia A`, compatible with `N`,
whose factor set is inflated from a factor set `β` on the inertia quotient `T/N`
(`TauCeti.IsProjectiveInertiaExtension`). Every projective representation `U` of `T/N` on a space
`X` with the inverse factor set `β⁻¹` gives a linear representation `ρ ⊗ U` of `T` on `A ⊗ X`
(`TauCeti.IsProjectiveInertiaExtension.tensorRep`), on which `N` acts through `A` alone.
`TauCeti.IsProjectiveInertiaExtension.tensorRepEquiv` shows that every irreducible representation of
`T` lying over an irreducible `A` is of this form, with `U` the conjugation action on
`Hom_N(A, W)`. This file proves the converse, for an irreducible `A` over an algebraically closed
field.

* `U` is recovered from `A ⊗ X`: the map `y ↦ (x ↦ x ⊗ y)` identifies `X` with
  `Hom_N(A, A ⊗ X)`, and it carries `U` to the conjugation action of `T/N` there. The proof
  compares this map with evaluation `A ⊗ Hom_N(A, A ⊗ X) → A ⊗ X`, which is injective by Burnside's
  density theorem and is a left inverse of `x ⊗ y ↦ x ⊗ (x' ↦ x' ⊗ y)`; since `A` is a nonzero
  vector space, tensoring with it reflects bijectivity.
* `A ⊗ X` is irreducible if and only if `U` is, that is, `X` is nonzero and has no `U`-invariant
  subspaces other than `0` and `X`. A `U`-invariant subspace `p` gives the subrepresentation
  `A ⊗ p`. Conversely, a nonzero subrepresentation of `A ⊗ X` contains, by density, all of
  `A ⊗ y` for some nonzero `y`, and the vectors `y` with this property form a `U`-invariant
  subspace.

Together with `TauCeti.IsProjectiveInertiaExtension.tensorRepEquiv`, this identifies the irreducible
representations of `T` lying over `A` with the irreducible projective representations of `T/N`
whose factor set is `β⁻¹`, the inverse of a cocycle representing the Clifford obstruction
`TauCeti.cliffordObstruction A`: `σ ↦ Hom_N(A, σ)` and `U ↦ A ⊗ U` are mutually inverse up to
isomorphism.

## Main definitions

* `TauCeti.IsProjectiveInertiaExtension.tmulIntertwining`: the linear map
  `X → Hom_N(A, A ⊗ X)`, `y ↦ (x ↦ x ⊗ y)`.

## Main results

* `TauCeti.IsProjectiveInertiaExtension.tensorRep_inclusion_tmul`: `N` acts on `A ⊗ X` through
  `A` alone.
* `TauCeti.IsProjectiveInertiaExtension.homAction_tmulIntertwining`: `tmulIntertwining` carries
  `U` to the conjugation action of the inertia quotient on `Hom_N(A, A ⊗ X)`.
* `TauCeti.IsProjectiveInertiaExtension.tmulIntertwining_bijective`: for an irreducible `A` over
  an algebraically closed field, `X ≃ Hom_N(A, A ⊗ X)`.
* `TauCeti.IsProjectiveInertiaExtension.isIrreducible_tensorRep_iff`: `A ⊗ X` is irreducible if
  and only if `U` is.
* `TauCeti.IsProjectiveInertiaExtension.eq_bot_or_eq_top_of_homAction_mem`: the multiplicity space
  `Hom_N(A, W)` of an irreducible `W` lying over `A` is an irreducible projective representation
  of the inertia quotient.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, AMS Chelsea (1976), Chapter 11.
* G. Karpilovsky, *Projective Representations of Finite Groups*, Marcel Dekker (1985).
-/

public section

namespace TauCeti

open CategoryTheory _root_.Representation TensorProduct

universe u v w

namespace IsProjectiveInertiaExtension

section Action

variable {k : Type u} {G : Type v} [CommRing k] [Group G] {N : Subgroup G} [N.Normal]
  {A : FDRep k N} {ρ : inertia A → A ≃ₗ[k] A}
  {β : inertia A ⧸ N.subgroupOf (inertia A) → inertia A ⧸ N.subgroupOf (inertia A) → kˣ}
  (h : IsProjectiveInertiaExtension A ρ β)
  {X : Type w} [AddCommMonoid X] [Module k X]
  {U : inertia A ⧸ N.subgroupOf (inertia A) → X ≃ₗ[k] X}
  (hU : IsProjectiveRep U fun a b ↦ (β a b)⁻¹)

include h

/-- **`N` acts on `A ⊗ X` through `A` alone**: `ρ` restricts to `A` on `N`, and `N` is trivial in
the inertia quotient, on which `U` is defined. -/
theorem tensorRep_inclusion_tmul (n : N) (x : A) (y : X) :
    h.tensorRep hU (Subgroup.inclusion (le_inertia A) n) (x ⊗ₜ y) = A.ρ n x ⊗ₜ y := by
  have hn : ((Subgroup.inclusion (le_inertia A) n : inertia A) :
      inertia A ⧸ N.subgroupOf (inertia A)) = 1 :=
    (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 n.2)
  rw [tensorRep_tmul, h.apply_inclusion, hn, hU.map_one, LinearEquiv.coe_one, id_eq]

/-- **Vectors of `X` as `N`-intertwiners into `A ⊗ X`**: `y` gives `x ↦ x ⊗ y`, an intertwiner
from `A` to the restriction of `ρ ⊗ U` to `N`. For an irreducible `A` over an algebraically closed
field this identifies `X` with `Hom_N(A, A ⊗ X)`
(`TauCeti.IsProjectiveInertiaExtension.tmulIntertwining_bijective`). -/
noncomputable def tmulIntertwining :
    X →ₗ[k] IntertwiningMap A.ρ ((h.tensorRep hU).comp (Subgroup.inclusion (le_inertia A))) where
  toFun y := ((TensorProduct.mk k A X).flip y).intertwiningMap_of_isIntertwiningMap _ _
    fun n x ↦ by simp [h.tensorRep_inclusion_tmul hU]
  map_add' y y' := IntertwiningMap.ext (LinearMap.ext fun x ↦ tmul_add x y y')
  map_smul' c y := IntertwiningMap.ext (LinearMap.ext fun x ↦ tmul_smul c x y)

@[simp]
theorem tmulIntertwining_apply_apply (y : X) (x : A) : h.tmulIntertwining hU y x = x ⊗ₜ y :=
  (rfl)

/-- **`tmulIntertwining` intertwines `U` with the conjugation action of the inertia quotient on
`Hom_N(A, A ⊗ X)`**, so `U` is recovered from `ρ ⊗ U`. -/
@[simp]
theorem homAction_tmulIntertwining (q : inertia A ⧸ N.subgroupOf (inertia A)) (y : X) :
    h.homAction (h.tensorRep hU) q (h.tmulIntertwining hU y) = h.tmulIntertwining hU (U q y) := by
  induction q using QuotientGroup.induction_on with | H t =>
  exact IntertwiningMap.ext (LinearMap.ext fun x ↦ by simp)

/-- The action of `k[N]` on the left factor of `A ⊗ X` preserves every subrepresentation of
`ρ ⊗ U`, since `N` acts on `A ⊗ X` through `A`. -/
private theorem rTensor_asAlgebraHom_mem {W : Subrepresentation (h.tensorRep hU)}
    (r : MonoidAlgebra k N) {w : A ⊗[k] X} (hw : w ∈ W) :
    (asAlgebraHom A.ρ r).rTensor X w ∈ W := by
  induction r using MonoidAlgebra.induction_on with
  | of n =>
    have hn : (A.ρ n).rTensor X = h.tensorRep hU (Subgroup.inclusion (le_inertia A) n) :=
      TensorProduct.ext' fun x y ↦ by simp [h.tensorRep_inclusion_tmul hU]
    rw [asAlgebraHom_of, hn]
    exact W.apply_mem_toSubmodule _ hw
  | add r r' hr hr' =>
    rw [map_add, LinearMap.rTensor_add, LinearMap.add_apply]
    exact W.toSubmodule.add_mem hr hr'
  | smul c r hr =>
    rw [map_smul, LinearMap.rTensor_smul, LinearMap.smul_apply]
    exact W.toSubmodule.smul_mem c hr

end Action

section Field

variable {k : Type u} {G : Type v} [Field k] [Group G] {N : Subgroup G} [N.Normal]
  {A : FDRep k N} {ρ : inertia A → A ≃ₗ[k] A}
  {β : inertia A ⧸ N.subgroupOf (inertia A) → inertia A ⧸ N.subgroupOf (inertia A) → kˣ}
  (h : IsProjectiveInertiaExtension A ρ β)
  {X : Type w} [AddCommGroup X] [Module k X]
  {U : inertia A ⧸ N.subgroupOf (inertia A) → X ≃ₗ[k] X}
  (hU : IsProjectiveRep U fun a b ↦ (β a b)⁻¹)
  [IsAlgClosed k] [Simple A]

include h

/-- **`X` is the multiplicity space of `A` in `A ⊗ X`**: for an irreducible `A` over an
algebraically closed field, `y ↦ (x ↦ x ⊗ y)` is a bijection `X → Hom_N(A, A ⊗ X)`. -/
theorem tmulIntertwining_bijective : Function.Bijective (h.tmulIntertwining hU) := by
  have : Nontrivial A := (FDRep.isIrreducible_of_simple A).nontrivial
  -- Evaluating `x ⊗ (x' ↦ x' ⊗ y)` returns `x ⊗ y`.
  have hleft (z : A ⊗[k] X) :
      h.evalTensor (h.tensorRep hU) ((h.tmulIntertwining hU).lTensor A z) = z := by
    induction z using TensorProduct.inductionOn with
    | tmul x y => simp
    | add z z' hz hz' => simp only [map_add, hz, hz']
  -- Evaluation is injective, so it is a two-sided inverse; `A ⊗ -` reflects bijectivity.
  have hinj := h.evalTensor_injective (h.tensorRep hU)
  rw [← Module.FaithfullyFlat.lTensor_bijective_iff_bijective k A]
  exact ⟨Function.LeftInverse.injective hleft, fun w ↦ ⟨_, hinj (hleft _)⟩⟩

/-- A `U`-invariant subspace `p` of `X` gives the subrepresentation `A ⊗ p` of `ρ ⊗ U`, so when
`ρ ⊗ U` is irreducible, `p` is `⊥` or `⊤`. -/
private theorem eq_bot_or_eq_top_of_isIrreducible (hirr : (h.tensorRep hU).IsIrreducible)
    (p : Submodule k X) (hp : ∀ q, ∀ y ∈ p, U q y ∈ p) : p = ⊥ ∨ p = ⊤ := by
  have : Nontrivial A := (FDRep.isIrreducible_of_simple A).nontrivial
  have hpt (t : inertia A) (y : X) (hy : y ∈ p) : U t y ∈ p := hp _ y hy
  have hcomm (t : inertia A) : (h.tensorRep hU t).comp (p.subtype.lTensor A) =
      (p.subtype.lTensor A).comp
        (TensorProduct.map (ρ t : A →ₗ[k] A) ((U t : X →ₗ[k] X).restrict (hpt t))) :=
    TensorProduct.ext' fun x y ↦ by simp
  let W : Subrepresentation (h.tensorRep hU) :=
    { toSubmodule := LinearMap.range (p.subtype.lTensor A)
      apply_mem_toSubmodule := fun t z hz ↦ by
        obtain ⟨z', rfl⟩ := hz
        exact ⟨_, (LinearMap.congr_fun (hcomm t) z').symm⟩ }
  rcases hirr.eq_bot_or_eq_top W with hW | hW
  · -- If `A ⊗ p = 0`, then `x ⊗ y = 0` for all `x` and all `y ∈ p`, so `p = 0`.
    refine Or.inl (eq_bot_iff.2 fun y hy ↦ (Submodule.mem_bot k).2 ?_)
    refine (h.tmulIntertwining_bijective hU).1 (IntertwiningMap.ext (LinearMap.ext fun x ↦ ?_))
    have hmem : x ⊗ₜ y ∈ W.toSubmodule := ⟨x ⊗ₜ ⟨y, hy⟩, rfl⟩
    rw [hW, Subrepresentation.toSubmodule_bot, Submodule.mem_bot] at hmem
    simpa using hmem
  · -- If `A ⊗ p = A ⊗ X`, then `p = X`, since `A ⊗ -` reflects surjectivity.
    have hsurj : Function.Surjective (p.subtype.lTensor A) := by
      rw [← LinearMap.range_eq_top]
      exact congrArg Subrepresentation.toSubmodule hW
    rw [Module.FaithfullyFlat.lTensor_surjective_iff_surjective k A] at hsurj
    exact Or.inr (eq_top_iff.2 fun y _ ↦ by
      obtain ⟨⟨y', hy'⟩, rfl⟩ := hsurj y
      exact hy')

/-- If the only `U`-invariant subspaces of `X` are `⊥` and `⊤`, a nonzero subrepresentation `W` of
`ρ ⊗ U` is everything: by density it contains `A ⊗ m` for some `m ≠ 0`, and the `y` with
`A ⊗ y ⊆ W` form a `U`-invariant subspace. -/
private theorem eq_top_of_ne_bot
    (hirr : ∀ p : Submodule k X, (∀ q, ∀ y ∈ p, U q y ∈ p) → p = ⊥ ∨ p = ⊤)
    {W : Subrepresentation (h.tensorRep hU)} (hW : W ≠ ⊥) : W = ⊤ := by
  refine Subrepresentation.toSubmodule_injective ?_
  obtain ⟨w, hw, hw0⟩ := W.toSubmodule.exists_mem_ne_zero_of_ne_bot fun hW' ↦
    hW (Subrepresentation.toSubmodule_injective (hW'.trans Subrepresentation.toSubmodule_bot.symm))
  obtain ⟨m, hm, hr⟩ := Representation.exists_ne_zero_forall_exists_rTensor_asAlgebraHom_eq_tmul
    A.ρ (FDRep.isIrreducible_of_simple A) hw0
  let p : Submodule k X := ⨅ x : A, W.toSubmodule.comap (TensorProduct.mk k A X x)
  have hmem_p {y : X} : y ∈ p ↔ ∀ x : A, x ⊗ₜ y ∈ W.toSubmodule := by
    simp [p, Submodule.mem_iInf]
  have hmp : m ∈ p := hmem_p.2 fun x ↦ by
    obtain ⟨r, hr⟩ := hr x
    rw [← hr]
    exact h.rTensor_asAlgebraHom_mem hU r hw
  have hp : p = ⊤ := by
    refine (hirr p fun q y hy ↦ ?_).resolve_left fun hp ↦ hm (by simpa [hp] using hmp)
    induction q using QuotientGroup.induction_on with | H t =>
    refine hmem_p.2 fun x ↦ ?_
    have hx := W.apply_mem_toSubmodule t (hmem_p.1 hy ((ρ t).symm x))
    rwa [tensorRep_tmul, LinearEquiv.apply_symm_apply] at hx
  -- So `W` contains every pure tensor.
  rw [Subrepresentation.toSubmodule_top, eq_top_iff, ← TensorProduct.span_tmul_eq_top,
    Submodule.span_le]
  rintro _ ⟨x, y, rfl⟩
  exact hmem_p.1 (hp ▸ Submodule.mem_top) x

/-- **`ρ ⊗ U` is irreducible exactly when `U` is**: for an irreducible `A` over an algebraically
closed field, the representation `ρ ⊗ U` of the inertia group on `A ⊗ X` is irreducible if and only
if `X` is nonzero and its only subspaces invariant under every `U q` are `⊥` and `⊤`. -/
theorem isIrreducible_tensorRep_iff :
    (h.tensorRep hU).IsIrreducible ↔
      Nontrivial X ∧ ∀ p : Submodule k X, (∀ q, ∀ y ∈ p, U q y ∈ p) → p = ⊥ ∨ p = ⊤ := by
  refine ⟨fun hirr ↦ ⟨?_, h.eq_bot_or_eq_top_of_isIrreducible hU hirr⟩, fun ⟨hX, hirr⟩ ↦ ?_⟩
  · -- `A ⊗ X` is nonzero, so `X` is.
    have := hirr.nontrivial
    by_contra hX
    rw [not_nontrivial_iff_subsingleton] at hX
    exact not_subsingleton (A ⊗[k] X) inferInstance
  refine { exists_pair_ne := ?_, eq_bot_or_eq_top := fun W ↦ or_iff_not_imp_left.2 fun hW ↦
    h.eq_top_of_ne_bot hU hirr hW }
  -- Some `x ⊗ y₀` with `y₀ ≠ 0` is nonzero, so `A ⊗ X ≠ 0`.
  obtain ⟨y₀, hy₀⟩ := exists_ne (0 : X)
  obtain ⟨x, hx⟩ : ∃ x : A, x ⊗ₜ y₀ ≠ 0 := by
    by_contra! H
    exact hy₀ ((h.tmulIntertwining_bijective hU).1
      (IntertwiningMap.ext (LinearMap.ext fun x ↦ by simpa using H x)))
  refine ⟨⊥, ⊤, fun hbt ↦ hx ?_⟩
  have hmem : x ⊗ₜ y₀ ∈ (⊤ : Subrepresentation (h.tensorRep hU)).toSubmodule := by
    rw [Subrepresentation.toSubmodule_top]
    exact Submodule.mem_top
  rwa [← hbt, Subrepresentation.toSubmodule_bot, Submodule.mem_bot] at hmem

/-- **The multiplicity space of an irreducible representation lying over `A` is an irreducible
projective representation of the inertia quotient**: if `σ` is irreducible and admits a nonzero
`N`-intertwiner from `A`, the only subspaces of `Hom_N(A, W)` invariant under the conjugation action
of the inertia quotient are `⊥` and `⊤`. -/
theorem eq_bot_or_eq_top_of_homAction_mem {W : Type w} [AddCommGroup W] [Module k W]
    (σ : Representation k (inertia A) W) [σ.IsIrreducible]
    {φ : IntertwiningMap A.ρ (σ.comp (Subgroup.inclusion (le_inertia A)))} (hφ : φ ≠ 0)
    (p : Submodule k (IntertwiningMap A.ρ (σ.comp (Subgroup.inclusion (le_inertia A)))))
    (hp : ∀ q, ∀ ψ ∈ p, h.homAction σ q ψ ∈ p) : p = ⊥ ∨ p = ⊤ :=
  ((h.isIrreducible_tensorRep_iff (h.isProjectiveRep_homAction σ)).1
    (isIrreducible_of_linearEquiv (h.tensorRepEquiv σ hφ).symm.toLinearEquiv
      (h.tensorRepEquiv σ hφ).symm.toIntertwiningMap.isIntertwining inferInstance)).2 p hp

end Field

end IsProjectiveInertiaExtension

end TauCeti
