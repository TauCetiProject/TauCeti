/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.Pi

/-!
# Finite-coordinate stabilization for linear maps into Noetherian modules

For any indexed family `v : ι → M` in a Noetherian `R`-module `M`, finitely many indices already
generate the full `R`-linear span of the family (`TauCeti.exists_finset_span_image_eq`).

When `R` is a commutative ring, `N` is a finitely generated `R`-module, and `M` is a Noetherian
`R`-module, `N →ₗ[R] M` is itself Noetherian (`isNoetherian_linearMap`). Applying finite-index
span stabilization to a family `φ : ι → N →ₗ[R] M` shows that the joint kernel of the whole family
already equals the joint kernel of finitely many of its members
(`TauCeti.exists_finset_iInf_ker_eq`). In particular, if the family separates points of `N`, a
finite subfamily already separates points of `N`
(`TauCeti.exists_finset_eq_zero_of_forall_apply_eq_zero`), and on any finitely generated submodule
`P` of a product `ι → M` into a Noetherian module, vanishing at a fixed finite set of coordinates
forces vanishing everywhere (`Submodule.exists_finset_eq_zero_of_apply_eq_zero`). Commutativity of
`R` is essential: over the first Weyl algebra `A₁(k)` in characteristic zero, `k[t]` is a simple
(hence Noetherian) left module while the evaluation maps `P ↦ P(tⁿ)` on the cyclic module `A₁(k)`
have trivial common kernel with every finite subintersection nonzero.

## References

* K. Buzzard, *Eigenvarieties*, in *L-functions and Galois representations*, London Math. Soc.
  Lecture Note Ser. 320 (2007), Lemma 2.2.
-/

public section

namespace TauCeti

/-- In a Noetherian module, the span of the range of an indexed family equals the span of its
image on some finite set of indices. -/
theorem exists_finset_span_image_eq (R : Type*) {M ι : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] [IsNoetherian R M] (v : ι → M) :
    ∃ S : Finset ι, Submodule.span R (v '' (S : Set ι)) = Submodule.span R (Set.range v) := by
  classical
  obtain ⟨T, hT, hspan⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset (R := R) (Set.range v)).1
      (IsNoetherian.noetherian _)
  rw [← Set.image_univ] at hT
  obtain ⟨S, -, hST⟩ := Finset.subset_set_image_iff.1 hT
  refine ⟨S, ?_⟩
  simpa only [← hST, Finset.coe_image] using hspan.symm

section CommRing

variable {R N M ι : Type*} [CommRing R] [AddCommGroup N] [AddCommGroup M]
  [Module R N] [Module R M] [Module.Finite R N] [IsNoetherian R M]

/-- **Joint-kernel stabilization**: for an indexed family of linear maps out of a finitely
generated module into a Noetherian module over a commutative ring, the intersection of all kernels
equals the intersection over a finite subset of indices (Buzzard, *Eigenvarieties*, Lemma 2.2). -/
theorem exists_finset_iInf_ker_eq (φ : ι → N →ₗ[R] M) :
    ∃ S : Finset ι, (⨅ i ∈ S, LinearMap.ker (φ i)) = ⨅ i, LinearMap.ker (φ i) := by
  obtain ⟨S, hS⟩ := exists_finset_span_image_eq R φ
  refine ⟨S, le_antisymm (fun x hx ↦ ?_) (iInf_mono fun i ↦ le_iInf fun _ ↦ le_rfl)⟩
  simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
  have hle : Submodule.span R (φ '' (S : Set ι)) ≤ LinearMap.ker (LinearMap.applyₗ x) := by
    rw [Submodule.span_le, Set.image_subset_iff]
    exact hx
  rw [hS] at hle
  intro i
  exact hle (Submodule.subset_span ⟨i, rfl⟩)

/-- If a family of linear maps out of a finitely generated module into a Noetherian module over a
commutative ring separates points, some finite subfamily already separates points. -/
theorem exists_finset_eq_zero_of_forall_apply_eq_zero (φ : ι → N →ₗ[R] M)
    (hsep : ∀ x, (∀ i, φ i x = 0) → x = 0) :
    ∃ S : Finset ι, ∀ x, (∀ i ∈ S, φ i x = 0) → x = 0 := by
  obtain ⟨S, hS⟩ := exists_finset_iInf_ker_eq φ
  refine ⟨S, fun x hx ↦ hsep x fun i ↦ ?_⟩
  have hx' : x ∈ ⨅ j, LinearMap.ker (φ j) := by
    rw [← hS]
    simpa only [Submodule.mem_iInf, LinearMap.mem_ker] using hx
  simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hx'
  exact hx' i

end CommRing

end TauCeti

/-- **Finite-coordinate detection** (Buzzard, *Eigenvarieties*, Lemma 2.2): on a finitely
generated submodule of a product of copies of a Noetherian module over a commutative ring, some
finite set of coordinates detects zero. -/
theorem Submodule.exists_finset_eq_zero_of_apply_eq_zero {R M ι : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [IsNoetherian R M] (P : Submodule R (ι → M))
    [Module.Finite R P] :
    ∃ S : Finset ι, ∀ f ∈ P, (∀ i ∈ S, f i = 0) → f = 0 := by
  obtain ⟨S, hS⟩ := TauCeti.exists_finset_eq_zero_of_forall_apply_eq_zero
    (fun i : ι ↦ (LinearMap.proj i).comp P.subtype)
    (fun p hp ↦ Subtype.ext (funext hp))
  exact ⟨S, fun f hf hfS ↦ congrArg Subtype.val (hS ⟨f, hf⟩ hfS)⟩
