/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Operations
public import TauCeti.Algebra.Algebra.Pi

/-!
# Invariants of a finite group separate orbits of rational points

Let a finite group `G` act on a commutative algebra `S` over a field `K` by `K`-algebra
automorphisms. The `K`-points of `S`, the `K`-algebra homomorphisms `χ : S →ₐ[K] K`, are permuted
by `G` through precomposition: `g` sends `χ` to `χ ∘ (g • ·)`. Two points in the same orbit agree
on every invariant. Conversely, two points in distinct orbits are separated by an invariant taking
the values `0` and `1` on them.

To construct it, interpolate on the finitely many points of the two orbits
(`AlgHom.surjective_pi_of_injective`): some `q : S` vanishes on the first orbit and equals `1` on
the second. The product `∏ g, g • q` of the translates of `q` is invariant and still takes the
values `0` and `1` on the two points. No hypothesis on the characteristic of `K` is needed, since
the separating invariant is a product of translates rather than an average.

For the action of a finite linear group on polynomial functions, this is the statement that the
invariant polynomials separate the orbits of points, which identifies the fibres of the quotient
map by the invariant ring.

## Main results

* `FixedPoints.exists_mem_subalgebra_eq_zero_and_eq_one`: points in distinct orbits are separated
  by an invariant with values `0` and `1`.
* `FixedPoints.forall_mem_subalgebra_eq_iff`: two points agree on every invariant exactly when
  they lie in the same orbit.

The construction is the one used for dot orbits of weights in
`TauCeti.exists_mem_dotInvariants_lift_eq_zero_one`, stated here for an arbitrary finite action.

## References

* H. Derksen, G. Kemper, *Computational Invariant Theory*, Springer (2002), Chapter 2.
-/

public section

namespace FixedPoints

variable {K S G : Type*} [Field K] [CommSemiring S] [Algebra K S] [Group G] [Finite G]
  [MulSemiringAction G S] [SMulCommClass G K S]

/-- **Invariants separate orbits of points.** If no translate `χ ∘ (g • ·)` of the point `χ` is
the point `ψ`, then some invariant takes the value `0` at `χ` and `1` at `ψ`. -/
theorem exists_mem_subalgebra_eq_zero_and_eq_one {χ ψ : S →ₐ[K] K}
    (h : ∀ g : G, χ.comp (MulSemiringAction.toAlgHom K S g) ≠ ψ) :
    ∃ p ∈ FixedPoints.subalgebra K S G, χ p = 0 ∧ ψ p = 1 := by
  classical
  let := Fintype.ofFinite G
  let t (φ : S →ₐ[K] K) (g : G) : S →ₐ[K] K := φ.comp (MulSemiringAction.toAlgHom K S g)
  -- Interpolate on both entire orbits before taking the product of the translates.
  let s : Finset (S →ₐ[K] K) := Finset.univ.image (t χ) ∪ Finset.univ.image (t ψ)
  obtain ⟨q, hq⟩ := AlgHom.surjective_pi_of_injective (fun φ : s ↦ (φ : S →ₐ[K] K))
    Subtype.val_injective (fun φ ↦ if ∃ g, t χ g = φ then 0 else 1)
  have hq' (φ : S →ₐ[K] K) (hφ : φ ∈ s) : φ q = if ∃ g, t χ g = φ then 0 else 1 :=
    congrFun hq ⟨φ, hφ⟩
  have hχ : χ q = 0 := by
    have h1 : t χ 1 = χ := AlgHom.ext fun x ↦ by simp [t]
    rw [← h1, hq' _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ 1)))]
    exact ite_eq_left ⟨1, rfl⟩
  have hψ (g : G) : ψ (g • q) = 1 := by
    have := hq' (t ψ g) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ g)))
    refine this.trans (ite_eq_right ?_)
    -- A coincidence `χ ∘ g' = ψ ∘ g` of translates would put `ψ` in the orbit of `χ`.
    rintro ⟨g', hg'⟩
    refine h (g' * g⁻¹) (AlgHom.ext fun x ↦ ?_)
    have := DFunLike.congr_fun hg' (g⁻¹ • x)
    simpa [t, mul_smul] using this
  refine ⟨∏ g : G, g • q, fun g' ↦ ?_, ?_, ?_⟩
  · -- Left multiplication by `g'` permutes the factors.
    rw [Finset.smul_prod']
    exact Fintype.prod_equiv (Equiv.mulLeft g') _ _ fun g ↦ by simp [mul_smul]
  · rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ 1) (by rw [one_smul, hχ])
  · rw [map_prod]
    exact Finset.prod_eq_one fun g _ ↦ hψ g

/-- **Invariants detect orbits of points.** Two points of `S` agree on every invariant exactly
when one is a translate of the other. -/
theorem forall_mem_subalgebra_eq_iff {χ ψ : S →ₐ[K] K} :
    (∀ p ∈ FixedPoints.subalgebra K S G, χ p = ψ p) ↔
      ∃ g : G, χ.comp (MulSemiringAction.toAlgHom K S g) = ψ := by
  constructor
  · intro heq
    by_contra h
    obtain ⟨p, hp, hχ, hψ⟩ := exists_mem_subalgebra_eq_zero_and_eq_one (not_exists.mp h)
    simpa [hχ, hψ] using heq p hp
  · rintro ⟨g, rfl⟩ p hp
    simp [(FixedPoints.mem_subalgebra.mp hp) g]

end FixedPoints
