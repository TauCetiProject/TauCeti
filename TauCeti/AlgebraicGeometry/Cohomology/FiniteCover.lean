/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.MayerVietoris
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Vanishing of cohomology above the size of a finite cover

Let `M` be a sheaf of modules on a scheme `X`, and let `U₁, …, U_r` be finitely many open
subsets such that every nonempty finite intersection `U_{i₁} ⊓ ⋯ ⊓ U_{iₖ}` has no cohomology
with coefficients in `M` in positive degrees (a *Leray cover*). Then `Hⁿ(U₁ ⊔ ⋯ ⊔ U_r, M) = 0`
for every `n ≥ r`. The proof is by induction on `r` through the Mayer–Vietoris sequence of
`U₁` and `U₂ ⊔ ⋯ ⊔ U_r`, whose intersection is covered by the `r - 1` opens `U₁ ⊓ Uᵢ`.

The main application is to quasi-coherent sheaves: on a locally Noetherian scheme with affine
diagonal (for instance a separated one), finite intersections of affine opens are affine, and
quasi-coherent sheaves have no higher cohomology on Noetherian affine opens. So if such a scheme
is covered by `r` affine opens, every quasi-coherent sheaf on it has vanishing cohomology in
degrees `n ≥ r`. This is the bound used for projective space `ℙᵈ_A` over a Noetherian ring `A`,
which is covered by its `d + 1` standard affine charts. The case of two opens is
`AlgebraicGeometry.Scheme.Modules.subsingleton_cohomology_of_two_le_of_isAffineOpen_of_isAffineHom`.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.subsingleton_cohomologyOn_sup_of_card_le`: for a finite
  Leray cover of the open subset `U₁ ⊔ ⋯ ⊔ U_r` by `r` opens, `Hⁿ(U₁ ⊔ ⋯ ⊔ U_r, M) = 0` for
  every `n ≥ r`;
* `AlgebraicGeometry.Scheme.Modules.subsingleton_cohomology_of_card_le`: the same for a finite
  Leray cover of `X`;
* `AlgebraicGeometry.Scheme.Modules.subsingleton_cohomology_of_isAffineOpen_of_card_le`: a
  quasi-coherent sheaf on a locally Noetherian scheme with affine diagonal covered by `r` affine
  opens has no cohomology in degrees `n ≥ r`.

## References

* R. Hartshorne, *Algebraic Geometry*, Exercise III.4.8 and the proof of Theorem III.5.2.
* The Stacks Project, Lemma 30.4.2 (tag 01XD).
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

open TauCeti TauCeti.AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules) {ι : Type*}

/-- **Vanishing above the size of a finite Leray cover.** Let `s` be a nonempty finite set of
indices of open subsets `U i` such that every nonempty finite intersection of the `U i` with
`i ∈ s` has no cohomology with coefficients in `M` in positive degrees. Then the union of the
`U i` with `i ∈ s` has no cohomology in degrees `n ≥ #s`. -/
theorem subsingleton_cohomologyOn_sup_of_card_le {s : Finset ι} (hs : s.Nonempty)
    (U : ι → X.Opens)
    (hU : ∀ t ⊆ s, t.Nonempty → ∀ i, Subsingleton (cohomologyOn M (i + 1) (t.inf U)))
    (n : ℕ) (hn : s.card ≤ n) : Subsingleton (cohomologyOn M n (s.sup U)) := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hs.card_pos; omega⟩
  -- Induct on `s`, for all families `U` and all degrees at once: the inductive step applies the
  -- hypothesis for the smaller index set to both `U` and the family of intersections `U a ⊓ U i`.
  induction hs using Finset.Nonempty.cons_induction generalizing U n with
  | singleton a =>
    simpa using hU {a} subset_rfl (Finset.singleton_nonempty a) n
  | cons a s ha hs ih =>
    rw [Finset.card_cons] at hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hs.card_pos; omega⟩
    have hsub : s ⊆ Finset.cons a s ha := Finset.subset_cons ha
    rw [Finset.sup_cons]
    refine subsingleton_cohomologyOn_sup_succ M (m + 1) ?_ ?_ ?_
    · rw [Finset.sup_inf_distrib_left]
      refine ih (fun i ↦ U a ⊓ U i) (fun t ht ht' j ↦ ?_) m (by omega)
      have h := hU (Finset.cons a t (fun h ↦ ha (ht h))) (Finset.cons_subset_cons.mpr ht)
        (Finset.cons_nonempty _) j
      rwa [Finset.inf_cons, ← Finset.inf_const ht' (U a), ← Finset.inf_inf] at h
    · simpa using hU {a} (by simp) (Finset.singleton_nonempty a) (m + 1)
    · exact ih U (fun t ht ↦ hU t (ht.trans hsub)) (m + 1) (by omega)

/-- **Vanishing above the size of a finite Leray cover of `X`.** If `X` is covered by the open
subsets `U i` with `i` in a nonempty finite set `s`, and every nonempty finite intersection of
these has no cohomology with coefficients in `M` in positive degrees, then `Hⁿ(X, M) = 0` for every
`n ≥ #s`. -/
theorem subsingleton_cohomology_of_card_le {s : Finset ι} (hs : s.Nonempty) (U : ι → X.Opens)
    (hcover : s.sup U = ⊤)
    (hU : ∀ t ⊆ s, t.Nonempty → ∀ i, Subsingleton (cohomologyOn M (i + 1) (t.inf U)))
    (n : ℕ) (hn : s.card ≤ n) : Subsingleton (Cohomology M n) := by
  have h := subsingleton_cohomologyOn_sup_of_card_le M hs U hU n hn
  rw [hcover] at h
  exact (cohomologyOnTopIso M n).symm.addCommGroupIsoToAddEquiv.toEquiv.subsingleton

/-- **Vanishing above the size of an affine cover.** A quasi-coherent sheaf of modules on a
locally Noetherian scheme with affine diagonal (for instance a separated one) which is covered by
`r` affine opens has no cohomology in degrees `n ≥ r`. -/
theorem subsingleton_cohomology_of_isAffineOpen_of_card_le [IsLocallyNoetherian X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] [M.IsQuasicoherent]
    {s : Finset ι} (hs : s.Nonempty) (U : ι → X.Opens) (hU : ∀ i ∈ s, IsAffineOpen (U i))
    (hcover : s.sup U = ⊤) (n : ℕ) (hn : s.card ≤ n) : Subsingleton (Cohomology M n) := by
  refine subsingleton_cohomology_of_card_le M hs U hcover (fun t ht ht' i ↦ ?_) n hn
  have hW : IsAffineOpen (t.inf U) := by
    rw [Finset.inf_eq_iInf]
    exact IsAffineOpen.biInf _ t.finite_toSet ht' fun j hj ↦ hU j (ht hj)
  have : IsNoetherianRing Γ(X, t.inf U) := IsLocallyNoetherian.component_noetherian ⟨_, hW⟩
  exact subsingleton_cohomologyOn_succ_of_isAffineOpen M hW i

end AlgebraicGeometry.Scheme.Modules
