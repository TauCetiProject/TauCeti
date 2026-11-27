/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Operations
public import TauCeti.Order.Superfluous
public import TauCeti.RingTheory.Jacobson.Module

import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Superfluous submodules

A submodule `N` of `M` is **superfluous** (also called *small*) when it is dispensable for
generating `M`: whenever `N ⊔ K = ⊤` for a submodule `K`, already `K = ⊤`. Superfluous submodules
are the dual notion to essential submodules, and an epimorphism `P ↠ M` is a projective cover
exactly when `P` is projective and its kernel is superfluous in `P`.

The lattice definition and its order-theoretic properties are in
`TauCeti.Order.Superfluous`. Here superfluousness is transported along linear maps and
characterized by containment in the radical when the submodule lattice is coatomic.

## Main results

* `TauCeti.isSuperfluous_pi_univ_iff`: a finite product of submodules is superfluous exactly
  when each factor is.
* `TauCeti.IsSuperfluous.map`: the image of a superfluous submodule under any linear map is
  superfluous; `TauCeti.isSuperfluous_map_equiv_iff` records that along an equivalence this is an
  equivalence.
* `TauCeti.IsSuperfluous.comap`: the preimage of a superfluous submodule under a surjection whose
  kernel is superfluous is again superfluous. This is what makes projective covers compose.
* `TauCeti.IsSuperfluous.surjective_of_surjective_comp` and
  `TauCeti.isSuperfluous_ker_iff_forall_surjective`: a surjection has superfluous kernel exactly
  when it is an *essential epimorphism*, that is, when every map into its source whose composite
  with it is onto is itself onto. This is the minimality that makes a projective cover a
  projective cover. Both directions need differences, so they are stated for modules over a
  semiring that are additive groups.
* `TauCeti.IsSuperfluous.le_coatom` and `TauCeti.IsSuperfluous.le_jacobson`: a superfluous
  submodule lies in every coatom, hence in the radical `Module.jacobson R M`.
* `TauCeti.isSuperfluous_iff_le_jacobson`: over a module whose submodule lattice is coatomic — in
  particular over a finitely generated module — the converse holds, so the superfluous submodules
  are exactly the submodules of the radical, and
  `TauCeti.isSuperfluous_jacobson` records that the radical itself is then superfluous.
* `TauCeti.isSuperfluous_smul_top_of_isNilpotent`: the form of Nakayama's lemma that needs no
  hypothesis on the module at all — a nilpotent ideal times any module is superfluous in it.
* `TauCeti.IsSuperfluous.finite_of_finite_quotient`: a module is finitely generated when its
  quotient by a superfluous submodule is.

## References

See I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
Algebras, Vol. 1*, Section I.4, and T. Y. Lam, *A First Course in Noncommutative Rings*, §24.
-/

public section

namespace TauCeti

universe u v w

section Semiring

variable {R : Type u} {M : Type v} {M₂ : Type w}
  [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M₂] [Module R M₂]

/-- Transport along a linear equivalence both preserves and reflects superfluity. -/
@[simp]
theorem isSuperfluous_map_equiv_iff {N : Submodule R M} (e : M ≃ₗ[R] M₂) :
    IsSuperfluous (N.map (e : M →ₗ[R] M₂)) ↔ IsSuperfluous N :=
  (Submodule.orderIsoMapComap e).isSuperfluous_iff N

/-- **Nakayama's lemma for a nilpotent ideal.** If `I` is a nilpotent ideal then `I • M` is
superfluous in `M`.

Unlike `TauCeti.isSuperfluous_jacobson`, which asks the submodule lattice of `M` to be coatomic
(for instance `M` finitely generated) and takes the radical of `M`, nilpotence of `I` buys the
conclusion for an arbitrary module: a submodule `K` with `I • M ⊔ K = ⊤` absorbs `I ^ k • M` into
`I ^ (k + 1) • M` for every `k`, and a power of `I` vanishes. -/
theorem isSuperfluous_smul_top_of_isNilpotent {I : Ideal R} (hI : IsNilpotent I) :
    IsSuperfluous (I • (⊤ : Submodule R M)) := by
  obtain ⟨m, hm⟩ := hI
  refine isSuperfluous_iff.mpr fun K hK ↦ ?_
  -- Multiplying `hK` by `I ^ k` trades the `k`-th power of `I` for the `(k + 1)`-st.
  have step : ∀ k : ℕ, I ^ k • (⊤ : Submodule R M) ≤ K ⊔ I ^ (k + 1) • (⊤ : Submodule R M) := by
    intro k
    calc I ^ k • (⊤ : Submodule R M)
        = I ^ k • (I • (⊤ : Submodule R M) ⊔ K) := by rw [hK]
      _ = I ^ k • (I • (⊤ : Submodule R M)) ⊔ I ^ k • K := Submodule.smul_sup ..
      _ = I ^ (k + 1) • (⊤ : Submodule R M) ⊔ I ^ k • K := by
            rw [Submodule.pow_succ, Submodule.mul_smul]
      _ ≤ I ^ (k + 1) • (⊤ : Submodule R M) ⊔ K := sup_le_sup_left Submodule.smul_le_right _
      _ = K ⊔ I ^ (k + 1) • (⊤ : Submodule R M) := sup_comm ..
  -- So `K` together with any power of `I` still spans, and the `m`-th power is zero.
  have key : ∀ k : ℕ, (⊤ : Submodule R M) ≤ K ⊔ I ^ k • (⊤ : Submodule R M) := by
    intro k
    induction k with
    | zero => rw [Submodule.pow_zero, Ideal.one_eq_top, Submodule.top_smul, sup_top_eq]
    | succ k ih => exact ih.trans (sup_le le_sup_left ((step k).trans (by simp)))
  simpa [hm] using key m

end Semiring

section AddCommGroup

variable {R : Type u} {M : Type v} {M₂ : Type w}
  [Semiring R] [AddCommGroup M] [Module R M] [AddCommGroup M₂] [Module R M₂]

/-- The image of a superfluous submodule under a linear map is superfluous. -/
theorem IsSuperfluous.map {N : Submodule R M} (hN : IsSuperfluous N) (f : M →ₗ[R] M₂) :
    IsSuperfluous (N.map f) := by
  refine isSuperfluous_iff.mpr fun K hK ↦ ?_
  -- Pulling `K` back gives a complement of `N` upstairs, so the preimage of `K` is everything.
  have hsup : Submodule.map f (N ⊔ K.comap f) ⊔ K = ⊤ := by
    rw [eq_top_iff, ← hK]
    exact sup_le_sup_right (Submodule.map_mono le_sup_left) K
  have hcomap : N ⊔ K.comap f = ⊤ := by
    rw [← Submodule.comap_map_sup_of_comap_le (f := f) (q := K) le_sup_right, hsup,
      Submodule.comap_top]
  have hcomapK : K.comap f = ⊤ := hN.eq_top_of_sup_eq_top hcomap
  -- Hence `K` already contains the image of `N`, and absorbs it in `hK`.
  have hle : N.map f ≤ K := Submodule.map_le_iff_le_comap.mpr (by rw [hcomapK]; exact le_top)
  rw [← hK]
  exact (sup_eq_right.mpr hle).symm

/-- The preimage of a superfluous submodule under a surjection whose kernel is itself superfluous
is superfluous. This is what makes projective covers compose. -/
theorem IsSuperfluous.comap {K : Submodule R M₂} (hK : IsSuperfluous K) {f : M →ₗ[R] M₂}
    (hf : Function.Surjective f) (hker : IsSuperfluous (LinearMap.ker f)) :
    IsSuperfluous (K.comap f) := by
  refine isSuperfluous_iff.mpr fun L hL ↦ ?_
  -- Pushing the complement `L` forward makes it a complement of `K` downstairs, ...
  have hmapL : L.map f = ⊤ := by
    refine hK.eq_top_of_sup_eq_top ?_
    rw [← Submodule.map_comap_eq_of_surjective hf K, ← Submodule.map_sup, hL, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr hf
  -- ... and pulling that equality back costs exactly the kernel.
  exact hker.eq_top_of_sup_eq_top
    (by rw [sup_comm, ← Submodule.comap_map_eq, hmapL, Submodule.comap_top])

/-- **A superfluous kernel is a minimality condition.** If `f : M →ₗ[R] M₂` has superfluous kernel
and `h : M₃ →ₗ[R] M` is such that `f ∘ₗ h` is onto, then `h` is already onto.

This is what makes a projective cover minimal; it is `TauCeti.IsProjectiveCover`'s workhorse, and
uses nothing about `f` beyond its kernel. -/
theorem IsSuperfluous.surjective_of_surjective_comp {M₃ : Type*} [AddCommMonoid M₃] [Module R M₃]
    {f : M →ₗ[R] M₂} (hf : IsSuperfluous (LinearMap.ker f)) {h : M₃ →ₗ[R] M}
    (hfh : Function.Surjective (f ∘ₗ h)) : Function.Surjective h := by
  rw [← LinearMap.range_eq_top]
  -- The range of `h` together with the superfluous `ker f` spans `M`, so the range is everything.
  exact hf.eq_top_of_sup_eq_top (by
    rw [sup_comm, ← Submodule.comap_map_eq, ← LinearMap.range_comp,
      LinearMap.range_eq_top.mpr hfh, Submodule.comap_top])

/-- **Superfluous kernels are exactly the essential epimorphisms.** A surjection `f : M →ₗ[R] M₂`
has superfluous kernel precisely when no map into `M` can compose onto `M₂` without already being
onto; the submodule inclusions of `M` witness the nontrivial direction, so it suffices to quantify
over sources in the universe of `M` (over larger sources the implication is
`TauCeti.IsSuperfluous.surjective_of_surjective_comp`). -/
theorem isSuperfluous_ker_iff_forall_surjective {f : M →ₗ[R] M₂} (hf : Function.Surjective f) :
    IsSuperfluous (LinearMap.ker f) ↔
      ∀ {M₃ : Type v} [AddCommMonoid M₃] [Module R M₃] (h : M₃ →ₗ[R] M),
        Function.Surjective (f ∘ₗ h) → Function.Surjective h := by
  constructor
  · intro hker _ _ _ h hfh
    exact hker.surjective_of_surjective_comp hfh
  · intro H
    refine isSuperfluous_iff.mpr fun K hK ↦ ?_
    have hmapK : Submodule.map f K = ⊤ := by
      have hall : Submodule.map f (LinearMap.ker f ⊔ K) = ⊤ := by
        rw [hK, Submodule.map_top, LinearMap.range_eq_top.mpr hf]
      rwa [Submodule.map_sup, LinearMap.le_ker_iff_map.mp le_rfl, bot_sup_eq] at hall
    have hs : Function.Surjective (f ∘ₗ K.subtype) := by
      rw [← LinearMap.range_eq_top, LinearMap.range_comp, Submodule.range_subtype, hmapK]
    have hsub : Function.Surjective (K.subtype) := H (M₃ := K) K.subtype hs
    exact (Submodule.range_subtype K).symm.trans (LinearMap.range_eq_top.mpr hsub)

/-- A finite product of superfluous submodules is superfluous. -/
theorem isSuperfluous_pi_univ {ι : Type*} [Finite ι] {M : ι → Type*} [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] {K : ∀ i, Submodule R (M i)} (hK : ∀ i, IsSuperfluous (K i)) :
    IsSuperfluous (Submodule.pi Set.univ K) := by
  classical
  rw [← Submodule.iSup_map_single]
  exact isSuperfluous_iSup fun i ↦ (hK i).map _

/-- A finite product of submodules is superfluous exactly when each factor is. -/
@[simp]
theorem isSuperfluous_pi_univ_iff {ι : Type*} [Finite ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] {K : ∀ i, Submodule R (M i)} :
    IsSuperfluous (Submodule.pi Set.univ K) ↔ ∀ i, IsSuperfluous (K i) := by
  classical
  exact ⟨fun h i ↦ (h.map (LinearMap.proj i)).mono fun x hx ↦
    ⟨Pi.single i x, Submodule.le_comap_single_pi (I := Set.univ) K hx, by simp⟩,
    isSuperfluous_pi_univ⟩

end AddCommGroup

section Ring

variable {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]

/-- A superfluous submodule is contained in the radical. -/
theorem IsSuperfluous.le_jacobson {N : Submodule R M} (hN : IsSuperfluous N) :
    N ≤ Module.jacobson R M := by
  rw [Module.jacobson_eq_radical]
  exact le_iInf₂ fun _ hm => hN.le_coatom hm

/-- Conversely, when every proper submodule of `M` sits under a maximal one, every submodule of the
radical is superfluous. -/
theorem isSuperfluous_of_le_jacobson [IsCoatomic (Submodule R M)] {N : Submodule R M}
    (h : N ≤ Module.jacobson R M) : IsSuperfluous N := by
  refine isSuperfluous_iff.mpr fun K hK ↦ ?_
  -- This is the nongenerating property of the order radical of a coatomic lattice.
  refine Order.radical_nongenerating (top_le_iff.mp ?_)
  rw [← hK, ← Module.jacobson_eq_radical]
  exact sup_le (le_sup_of_le_right h) le_sup_left

/-- Over a module with coatomic submodule lattice — for instance a finitely generated one — the
superfluous submodules are exactly the submodules of the radical.

This is the simp normal form of superfluity wherever the comparison is available, at low priority
so that the shape-specific lemmas above (`TauCeti.isSuperfluous_bot`,
`TauCeti.isSuperfluous_sup_iff`, `TauCeti.isSuperfluous_top_iff`,
`TauCeti.isSuperfluous_map_equiv_iff`) still fire first on the submodules they match. -/
@[simp low]
theorem isSuperfluous_iff_le_jacobson [IsCoatomic (Submodule R M)] {N : Submodule R M} :
    IsSuperfluous N ↔ N ≤ Module.jacobson R M :=
  ⟨IsSuperfluous.le_jacobson, isSuperfluous_of_le_jacobson⟩

/-- The radical of a module with coatomic submodule lattice — for instance a finitely generated
one — is superfluous; this is the form of Nakayama's lemma that the theory of projective covers
runs on. -/
theorem isSuperfluous_jacobson [IsCoatomic (Submodule R M)] :
    IsSuperfluous (Module.jacobson R M) :=
  isSuperfluous_of_le_jacobson le_rfl

/-- **Finite generation lifts across a superfluous submodule.** If `N` is superfluous in `M` and
`M ⧸ N` is finitely generated, then `M` is finitely generated. With
`TauCeti.isSuperfluous_smul_top_of_isNilpotent` this is Nakayama's lemma for a nilpotent ideal
`I` in the form that needs no finiteness of `M`: `M` is finitely generated as soon as `M ⧸ I • M`
is. -/
theorem IsSuperfluous.finite_of_finite_quotient {N : Submodule R M} (hN : IsSuperfluous N)
    [Module.Finite R (M ⧸ N)] : Module.Finite R M := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M ⧸ N)
  choose t ht using fun i ↦ N.mkQ_surjective (s i)
  -- Lifts of generators of `M ⧸ N` span a supplement of `N`, which is everything.
  refine ⟨⟨Finset.univ.image t, hN.eq_top_of_sup_eq_top ?_⟩⟩
  rw [← Submodule.map_mkQ_eq_top, Submodule.map_span, ← hs]
  congr 1
  ext
  simp [← ht]

end Ring

end TauCeti
