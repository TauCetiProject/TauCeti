/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Invariant.Profinite

/-!
# Images of decomposition and inertia groups along profinite quotients

Let `G` act on an `R`-algebra `S` and `G'` on `R`, and let `f : G →* G'` be surjective with
`algebraMap R S (f g • x) = g • algebraMap R S x`. Suppose a subgroup `H ≤ ker f` has `R` as its
invariants. Mathlib's `Ideal.map_stabilizer_of_surjective` and
`Ideal.map_inertia_of_surjective` show that `f` maps the decomposition and inertia groups of a
prime `q` of `S` onto those of `p = q ∩ R`, when `H` is finite.

This file proves the same statements when `H` is a compact totally disconnected topological
group acting continuously on `S` with the discrete topology, the setting of infinite Galois
theory. The proofs are Mathlib's, with the finite transitivity and residue-field surjectivity
theorems replaced by their profinite versions
`Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite` and
`Ideal.Quotient.stabilizerHom_surjective_of_profinite`.

## Main results

* `Ideal.map_stabilizer_of_surjective_of_profinite`: `f(D_q) = D_p`.
* `Ideal.map_inertia_of_surjective_of_profinite`: `f(I_q) = I_p`.
-/

public section

open MulAction Pointwise

namespace Ideal

variable {R S G G' : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Group G] [Group G'] [MulSemiringAction G S] [MulSemiringAction G' R]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace S] [DiscreteTopology S]
  [ContinuousSMul G S]
  (f : G →* G') (H : Subgroup G) [CompactSpace H] [TotallyDisconnectedSpace H]
  [Algebra.IsInvariant R S H]
  (p : Ideal R) (q : Ideal S) [q.LiesOver p] [q.IsPrime]

/-- **Decomposition groups along a profinite quotient.** If `f : G →* G'` is surjective, the
action of `G'` on `R` is compatible with that of `G` on `S`, and a compact totally disconnected
subgroup `H ≤ ker f` has invariants `R`, then `f` maps the decomposition group of `q` onto that of
`p = q ∩ R`. -/
theorem map_stabilizer_of_surjective_of_profinite (hf_surj : Function.Surjective f)
    (hf_ker : H ≤ f.ker) (hf : ∀ g x, algebraMap R S (f g • x) = g • algebraMap R S x) :
    (stabilizer G q).map f = stabilizer G' p := by
  replace hf_ker (h : H) : f h = 1 := hf_ker h.property
  have : SMulCommClass H R S := ⟨fun h x y ↦ by simp [Algebra.smul_def, H.smul_def, ← hf, hf_ker]⟩
  apply le_antisymm
  · rintro - ⟨g, hg, rfl⟩
    ext x
    rw [SetLike.mem_coe, mem_stabilizer_iff] at hg
    simp_rw [mem_pointwise_smul_iff_inv_smul_mem, over_def q p, mem_under, ← map_inv, hf,
      ← mem_pointwise_smul_iff_inv_smul_mem, hg]
  · intro g hg
    obtain ⟨g, rfl⟩ := hf_surj g
    have : (g • q).under R = q.under R := by
      ext x
      rw [mem_under, mem_pointwise_smul_iff_inv_smul_mem, ← hf, ← mem_under, ← over_def q p,
        map_inv, ← mem_pointwise_smul_iff_inv_smul_mem, hg]
    obtain ⟨g', hg'⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := R)
      (G := H) (g • q) q this
    exact ⟨g' * g, by simpa [mul_smul, eq_comm], by simp [hf_ker]⟩

/-- **Inertia groups along a profinite quotient.** If `f : G →* G'` is surjective, the action of
`G'` on `R` is compatible with that of `G` on `S`, and a compact totally disconnected subgroup
`H ≤ ker f` has invariants `R`, then `f` maps the inertia group of `q` onto that of
`p = q ∩ R`. -/
theorem map_inertia_of_surjective_of_profinite (hf_surj : Function.Surjective f)
    (hf_ker : H ≤ f.ker) (hf : ∀ g x, algebraMap R S (f g • x) = g • algebraMap R S x) :
    (q.inertia G).map f = p.inertia G' := by
  have h_stab := (map_stabilizer_of_surjective_of_profinite f H p q hf_surj hf_ker hf).ge
  replace hf_ker (h : H) : f h = 1 := hf_ker h.property
  have : SMulCommClass H R S := ⟨fun h x y ↦ by simp [Algebra.smul_def, H.smul_def, ← hf, hf_ker]⟩
  apply le_antisymm
  · rintro - ⟨g, hg, rfl⟩ x
    simpa [over_def q p, map_sub, hf] using hg (algebraMap R S x)
  · intro g hg
    obtain ⟨g, rfl⟩ : ∃ g' : stabilizer G q, f g' = g := by
      simpa using h_stab.ge (p.inertia_le_stabilizer hg)
    let φ : (S ⧸ q) ≃ₐ[R ⧸ p] (S ⧸ q) :=
    { __ := Quotient.stabilizerHom q (q.under ℤ) G g
      commutes' x := by
        obtain ⟨x, rfl⟩ := Quotient.mk_surjective x
        specialize hg x
        rw [Submodule.mem_toAddSubgroup, over_def q p, mem_under, map_sub, hf, ← Quotient.eq] at hg
        simpa }
    obtain ⟨g', hg'⟩ := Quotient.stabilizerHom_surjective_of_profinite (G := H) p q φ
    let v : stabilizer G q := ⟨g', g'.property⟩⁻¹ * g
    refine ⟨v, ?_, by simp [v, hf_ker]⟩
    rw [SetLike.mem_coe, coe_mem_inertia, ← Quotient.ker_stabilizerHom q (q.under ℤ) G,
      MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
    rw [AlgEquiv.ext_iff] at hg' ⊢
    assumption

end Ideal
