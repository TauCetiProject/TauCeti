/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.RootsOfUnity.PadicTateTwist

/-!
# `ℤ_p(1) / p^n ≅ μ_{p^n}`

Let `K` be a commutative monoid. The projection `TauCeti.PadicTateTwist.proj n` of the `p`-adic
Tate twist `ℤ_p(1) = PadicTateTwist p K` to the group `μ_{p^n}(K)` of `p^n`-th roots of unity has
kernel `p^n ℤ_p(1)` (`TauCeti.PadicTateTwist.ker_proj`). When `K` has enough `p`-power
roots of unity it is surjective (`TauCeti.PadicTateTwist.proj_surjective`), so it induces
`ℤ_p(1) / p^n ≅ μ_{p^n}(K)` (`TauCeti.PadicTateTwist.quotientEquivRootsOfUnity`). For a field
extension `K / F`, the projection intertwines the Galois action on `ℤ_p(1)` with the action of
`Gal(K / F)` on `μ_{p^n}(K)` (`TauCeti.PadicTateTwist.proj_galoisRepresentation`), so the
isomorphism is Galois-equivariant
(`TauCeti.PadicTateTwist.quotientEquivRootsOfUnity_galoisRepresentation`).

## Main definitions

* `TauCeti.PadicTateTwist.quotientEquivRootsOfUnity n`: `ℤ_p(1) / ker (proj n) ≃+ μ_{p^n}(K)`.

## Main results

* `TauCeti.PadicTateTwist.proj_eq_zero_iff`, `TauCeti.PadicTateTwist.ker_proj`: the kernel of
  `proj n` is `p^n ℤ_p(1)`.
* `TauCeti.PadicTateTwist.proj_surjective`: `proj n` is surjective.
* `TauCeti.PadicTateTwist.natCard_quotient_ker_proj`: `ℤ_p(1) / p^n` has `p^n` elements.
* `TauCeti.PadicTateTwist.proj_galoisRepresentation`: `proj n` is Galois-equivariant.
* `TauCeti.PadicTateTwist.quotientEquivRootsOfUnity_galoisRepresentation`: so is the quotient
  isomorphism.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7.
-/

public section

noncomputable section

namespace TauCeti

namespace PadicTateTwist

variable {p : ℕ} {K : Type*} [CommMonoid K]

/-- **The kernel of the projection to `μ_{p^n}` is `p^n ℤ_p(1)`.** -/
theorem proj_eq_zero_iff {x : PadicTateTwist p K} {n : ℕ} :
    proj n x = 0 ↔ ∃ y : PadicTateTwist p K, x = p ^ n • y := by
  rw [proj_def, AddEquiv.map_eq_zero_iff]
  exact TateModule.proj_eq_zero_iff

/-- **The kernel of the projection to `μ_{p^n}` is the subgroup `p^n ℤ_p(1)`.** -/
theorem ker_proj (n : ℕ) :
    (proj (p := p) (K := K) n).ker =
      (nsmulAddMonoidHom (p ^ n) : PadicTateTwist p K →+ PadicTateTwist p K).range := by
  ext x
  rw [AddMonoidHom.mem_ker, proj_eq_zero_iff, AddMonoidHom.mem_range]
  simp [eq_comm]

/-- **Every `p^n`-th root of unity is a component of `ℤ_p(1)`**, when `K` has enough `p`-power
roots of unity. -/
theorem proj_surjective [NeZero p] [∀ n, HasEnoughRootsOfUnity K (p ^ n)] (n : ℕ) :
    Function.Surjective (proj (p := p) (K := K) n) := by
  rw [show ⇑(proj (p := p) (K := K) n) = levelAddEquivRootsOfUnity n ∘ TateModule.proj n from
    funext (proj_def n)]
  exact (levelAddEquivRootsOfUnity n).surjective.comp <| TateModule.proj_surjective
    (TateModule.tateModuleTransition_surjective_of_natCard (r := 1) (NeZero.ne p)
      fun k ↦ by simpa using natCard_tateModuleLevel (K := K) k) n

/-- **`ℤ_p(1) / p^n ≅ μ_{p^n}`**: the projection to `μ_{p^n}` induces an isomorphism from the
quotient by its kernel, which is `p^n ℤ_p(1)` (`ker_proj`). -/
def quotientEquivRootsOfUnity [NeZero p] [∀ n, HasEnoughRootsOfUnity K (p ^ n)] (n : ℕ) :
    PadicTateTwist p K ⧸ (proj (p := p) (K := K) n).ker ≃+ Additive (rootsOfUnity (p ^ n) K) :=
  QuotientAddGroup.quotientKerEquivOfSurjective _ (proj_surjective n)

@[simp]
theorem quotientEquivRootsOfUnity_mk [NeZero p] [∀ n, HasEnoughRootsOfUnity K (p ^ n)] (n : ℕ)
    (x : PadicTateTwist p K) :
    quotientEquivRootsOfUnity n (x : PadicTateTwist p K ⧸ (proj (p := p) (K := K) n).ker) =
      proj n x :=
  (rfl)

/-- **`ℤ_p(1) / p^n` has `p^n` elements** when `K` has enough `p`-power roots of unity; the
kernel of `proj n` is `p^n ℤ_p(1)` by `ker_proj`. -/
theorem natCard_quotient_ker_proj [NeZero p] [∀ n, HasEnoughRootsOfUnity K (p ^ n)] (n : ℕ) :
    Nat.card (PadicTateTwist p K ⧸ (proj (p := p) (K := K) n).ker) = p ^ n :=
  (Nat.card_congr ((quotientEquivRootsOfUnity n).trans
    (levelAddEquivRootsOfUnity n).symm).toEquiv).trans (natCard_tateModuleLevel n)

section Galois

variable {F L : Type*} [Field F] [Field L] [Algebra F L] [Fact p.Prime]

/-- **The projection to `μ_{p^n}` is Galois-equivariant**: it carries the Galois action on
`ℤ_p(1)` to the action of `Gal(L / F)` on `μ_{p^n}(L)`. -/
theorem proj_galoisRepresentation (σ : L ≃ₐ[F] L) (x : PadicTateTwist p L) (n : ℕ) :
    proj n (galoisRepresentation (F := F) σ x) =
      Additive.ofMul (restrictRootsOfUnity σ (p ^ n) (proj n x).toMul) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  simp only [coe_proj, toMul_ofMul, restrictRootsOfUnity_coe_apply]
  exact coe_tateModuleProj_galoisRepresentation σ x n

/-- **`ℤ_p(1) / p^n ≅ μ_{p^n}` is Galois-equivariant.** -/
theorem quotientEquivRootsOfUnity_galoisRepresentation
    [∀ n, HasEnoughRootsOfUnity L (p ^ n)] (σ : L ≃ₐ[F] L) (x : PadicTateTwist p L) (n : ℕ) :
    quotientEquivRootsOfUnity n
        ((galoisRepresentation (F := F) σ x : PadicTateTwist p L) :
          PadicTateTwist p L ⧸ (proj (p := p) (K := L) n).ker) =
      Additive.ofMul (restrictRootsOfUnity σ (p ^ n)
        (quotientEquivRootsOfUnity n (x : PadicTateTwist p L ⧸ (proj n).ker)).toMul) := by
  rw [quotientEquivRootsOfUnity_mk, quotientEquivRootsOfUnity_mk]
  exact proj_galoisRepresentation σ x n

end Galois

end PadicTateTwist

end TauCeti
