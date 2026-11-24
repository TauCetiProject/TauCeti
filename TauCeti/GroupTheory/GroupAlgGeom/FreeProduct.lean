/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Discrimination
import Mathlib.Data.Finset.Union
import TauCeti.GroupTheory.Coprod.NormalForm
import TauCeti.GroupTheory.Coprod.Reduced

/-!
# Discrimination of free products

Regard the free product `H ∗ K` as a group with coefficients in its first factor. If `K` is
discriminated by a group `L`, then `H ∗ K` is discriminated by `H ∗ L` over `H`. Given finitely many
nonidentity elements of `H ∗ K`, write each as a reduced word and choose one homomorphism
`φ : K →* L` that keeps every letter from `K` of these words away from `1`. The homomorphism
`H ∗ K →* H ∗ L` that is the identity on `H` and `φ` on `K` sends each word to a nonempty reduced
word, which is not `1`.

With `L` a free group, this reduces the discrimination of `H ∗ K` by `H`, for a fully residually
free group `K`, to the discrimination of the free `H`-groups `H ∗ F(X)` by `H`.

## Main results

* `TauCeti.GroupAlgGeom.IsDiscriminatedBy.coprod_inl`: if `K` is discriminated by `L`, then
  `H ∗ K` is discriminated by `H ∗ L` over `H`.

## References

* C. Champetier, V. Guirardel, *Limit groups as limits of free groups*, Israel J. Math. 146
  (2005), §2.9, Lemma 2.23 (the same normal-form argument for limits of marked groups).
* O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group II: Systems in
  triangular quasi-quadratic form and description of residually free groups*, J. Algebra 200
  (1998), proof of Theorem 4 (where this discrimination is used).
-/

public section

open Monoid.Coprod

namespace TauCeti.GroupAlgGeom

variable {K L : Type*} [Group K] [Group L]

/-- If `K` is discriminated by `L`, then the free product `H ∗ K` is discriminated by `H ∗ L` over
`H`: finitely many nonidentity elements of `H ∗ K` survive under one homomorphism `H ∗ K →* H ∗ L`
that is the identity on `H`. -/
theorem IsDiscriminatedBy.coprod_inl (h : IsDiscriminatedBy (1 : Unit →* K) (1 : Unit →* L))
    (H : Type*) [Group H] : IsDiscriminatedBy (inl : H →* H ∗ K) (inl : H →* H ∗ L) := by
  classical
  rw [isDiscriminatedBy_def] at h ⊢
  intro s hs
  choose R hc h₁ h₂ hR using fun x : H ∗ K => exists_reduced_list_mk_eq x
  -- The letters from `K` of the reduced words `R x` of the elements `x ∈ s`.
  let T : Finset K := s.biUnion fun x => ((R x).filterMap Sum.getRight?).toFinset
  have hT {k : K} : k ∈ T ↔ ∃ x ∈ s, Sum.inr k ∈ R x := by simp [T]
  -- One homomorphism `φ : K →* L` keeps all of them away from `1`, and `id ∗ φ` sends each
  -- `R x` to a nonempty reduced word.
  obtain ⟨φ, hφ⟩ := h T fun k hk => by
    obtain ⟨x, -, hk⟩ := hT.1 hk
    rintro rfl
    exact h₂ x hk
  refine ⟨⟨map (.id H) φ, fun _ => by simp⟩, fun x hx => ?_⟩
  rw [← hR x]
  exact map_mk_ofList_ne_one _ _ (fun hn => hs x hx (by simpa [hn] using (hR x).symm)) (hc x)
    (fun m hm h1 => h₁ x (by rw [MonoidHom.id_apply] at h1; rwa [h1] at hm))
    fun k hk => hφ k (hT.2 ⟨x, hx, hk⟩)

end TauCeti.GroupAlgGeom
